import Std
import Lean.Elab.Tactic

/-!
# Small-order biplanar coloring

Target toolchain: Lean 4.34.0. No mathlib dependency.

This is a PARTIAL formalization. Arithmetic and local coloring arguments have
proof bodies. The final graph theorem is conditional on `GraphReductionInputs`
and `FiniteCaseInputs`; neither input structure is instantiated here.

In particular, the external Python enumerations and HiGHS runs are NOT imported
as Lean proofs. There are no project axioms, `sorry`, or `native_decide` calls.
See README.md for the exact boundary and the build-validation status.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace EarthMoon

/-! ## Finite graph definitions -/

structure Graph (n : Nat) where
  edge : Fin n → Fin n → Bool
  symm : ∀ u v, edge u v = edge v u
  loopless : ∀ u, edge u u = false

def Adj {n : Nat} (G : Graph n) (u v : Fin n) : Prop := G.edge u v = true

def sumFin (n : Nat) (f : Fin n → Nat) : Nat :=
  (List.ofFn f).foldr (fun x acc => x + acc) 0

def edgeCount {n : Nat} (G : Graph n) : Nat :=
  sumFin n fun u => sumFin n fun v =>
    if u.val < v.val then if G.edge u v then 1 else 0 else 0

def degree {n : Nat} (G : Graph n) (u : Fin n) : Nat :=
  sumFin n fun v => if G.edge u v then 1 else 0

def Proper {n k : Nat} (G : Graph n) (c : Fin n → Fin k) : Prop :=
  ∀ u v, Adj G u v → c u ≠ c v

def Colorable {n : Nat} (G : Graph n) (k : Nat) : Prop :=
  ∃ c : Fin n → Fin k, Proper G c

def Contains {n : Nat} (H G : Graph n) : Prop :=
  ∀ u v, Adj H u v → Adj G u v

def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

structure Embedding {m n : Nat} (H : Graph m) (G : Graph n) where
  map : Fin m → Fin n
  injective : Injective map
  preserves : ∀ u v, Adj H u v → Adj G (map u) (map v)

def Isomorphic {n : Nat} (G H : Graph n) : Prop :=
  ∃ f : Fin n → Fin n, ∃ g : Fin n → Fin n,
    (∀ u, g (f u) = u) ∧ (∀ u, f (g u) = u) ∧
    (∀ u v, G.edge u v = H.edge (f u) (f v))

def Critical {n : Nat} (G : Graph n) (k : Nat) : Prop :=
  Colorable G k ∧ ¬ Colorable G (k - 1) ∧
  ∀ (m : Nat) (H : Graph m),
    Nonempty (Embedding H G) →
    (m < n ∨ edgeCount H < edgeCount G) → Colorable H (k - 1)

def CliqueFree {n : Nat} (G : Graph n) (k : Nat) : Prop :=
  ∀ f : Fin k → Fin n, Injective f →
    ¬ (∀ i j, i ≠ j → Adj G (f i) (f j))

def IndependentTriple {n : Nat} (G : Graph n) : Prop :=
  ∃ u v w : Fin n,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
    ¬ Adj G u v ∧ ¬ Adj G u w ∧ ¬ Adj G v w

def AlphaAtMost {n : Nat} (G : Graph n) (k : Nat) : Prop :=
  ∀ f : Fin (k + 1) → Fin n, Injective f →
    ¬ (∀ i j, i ≠ j → ¬ Adj G (f i) (f j))

def TriangleFree {n : Nat} (G : Graph n) : Prop :=
  ∀ u v w, ¬ (Adj G u v ∧ Adj G v w ∧ Adj G w u)

def MaximalTriangleFree {n : Nat} (G : Graph n) : Prop :=
  TriangleFree G ∧ ∀ u v, u ≠ v → ¬ Adj G u v →
    ∃ w, Adj G u w ∧ Adj G v w

/-- A planar predicate is a parameter, not an asserted implementation of planarity. -/
abbrev PlanarPredicate := (n : Nat) → Graph n → Prop

/-- The two layers are disjoint and their union is exactly G. -/
def Biplanar (P : PlanarPredicate) {n : Nat} (G : Graph n) : Prop :=
  ∃ L₁ L₂ : Graph n,
    P n L₁ ∧ P n L₂ ∧
    (∀ u v, Adj G u v ↔ Adj L₁ u v ∨ Adj L₂ u v) ∧
    (∀ u v, ¬ (Adj L₁ u v ∧ Adj L₂ u v))

theorem colorable_subgraph {n k : Nat} {H G : Graph n}
    (hHG : Contains H G) (hG : Colorable G k) : Colorable H k := by
  rcases hG with ⟨c, hc⟩
  exact ⟨c, fun u v huv => hc u v (hHG u v huv)⟩

/-- Soundness of a coloring-separation clause. -/
theorem coloring_cut_sound {n k : Nat} (G : Graph n)
    (hG : ¬ Colorable G k) (c : Fin n → Fin k) :
    ∃ u v, Adj G u v ∧ c u = c v := by
  apply Classical.byContradiction
  intro h
  apply hG
  refine ⟨c, ?_⟩
  intro u v huv heq
  exact h ⟨u, v, huv, heq⟩

/-! ## Arithmetic in Sections 2–4 and 7 -/

def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- Used only in the stated Gallai range; subtraction is natural subtraction. -/
def gallaiBound (k n : Nat) : Nat :=
  chooseTwo n - (n - k) * (n - k) - 1

def biplanarBudget (n : Nat) : Nat := 6 * n - 12

def tripleBound (n t : Nat) : Nat :=
  27 + gallaiBound 9 t + 6 * (n - 3 - t) - chooseTwo (n - 3 - t)

theorem gallai_small_table :
    [gallaiBound 10 12, gallaiBound 10 13,
     gallaiBound 10 14, gallaiBound 10 15] = [61, 68, 74, 79] := by decide

theorem triple_table_16 :
    [tripleBound 16 11, tripleBound 16 12, tripleBound 16 13] =
      [88, 89, 88] := by decide

theorem triple_table_17 :
    [tripleBound 17 11, tripleBound 17 12,
     tripleBound 17 13, tripleBound 17 14] = [92, 94, 94, 92] := by decide

theorem triple_table_18 :
    [tripleBound 18 11, tripleBound 18 12, tripleBound 18 13,
     tripleBound 18 14, tripleBound 18 15] = [95, 98, 99, 98, 95] := by decide

theorem small_order_arithmetic {n m : Nat}
    (hn₁ : 12 ≤ n) (hn₂ : n ≤ 15)
    (hlow : gallaiBound 10 n ≤ m) (hhigh : m ≤ biplanarBudget n) : False := by
  have checked : ∀ a : Fin 16,
      12 ≤ a.val → biplanarBudget a.val < gallaiBound 10 a.val := by decide
  -- Give omega the inequality on n, not an unreduced Fin projection.
  have h : biplanarBudget n < gallaiBound 10 n :=
    checked ⟨n, by omega⟩ hn₁
  omega

theorem triple_exceeds_budget_before18 {n t : Nat}
    (hn₁ : 16 ≤ n) (hn₂ : n ≤ 17)
    (ht₁ : 11 ≤ t) (ht₂ : t ≤ n - 3) :
    biplanarBudget n < tripleBound n t := by
  have checked : ∀ a b : Fin 20,
      16 ≤ a.val → a.val ≤ 17 → 11 ≤ b.val → b.val ≤ a.val - 3 →
      biplanarBudget a.val < tripleBound a.val b.val := by decide
  exact checked ⟨n, by omega⟩ ⟨t, by omega⟩ hn₁ hn₂ ht₁ ht₂

theorem order18_triple_cases {t m : Nat}
    (ht₁ : 11 ≤ t) (ht₂ : t ≤ 15)
    (hlow : tripleBound 18 t ≤ m) (hhigh : m ≤ 96) : t = 11 ∨ t = 15 := by
  have checked : ∀ a : Fin 16,
      11 ≤ a.val → tripleBound 18 a.val ≤ 96 → a.val = 11 ∨ a.val = 15 := by decide
  exact checked ⟨t, by omega⟩ ht₁ (Nat.le_trans hlow hhigh)

theorem one_unit_slack {a b c d m : Nat}
    (hcount : m = 95 + a + b + c + d) (hcap : m ≤ 96) :
    a + b + c + d ≤ 1 := by omega

def OrderPart (n : Nat) : Prop := n = 1 ∨ (5 ≤ n ∧ n % 2 = 1)

/-- Completeness of the *integer* component-order table, not Gallai decomposition. -/
theorem component_orders16 {a b c d : Nat}
    (_ha : OrderPart a) (hb : OrderPart b) (hc : OrderPart c) (hd : OrderPart d)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hs : a + b + c + d = 16) :
    (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 13) ∨
    (a = 1 ∧ b = 1 ∧ c = 5 ∧ d = 9) ∨
    (a = 1 ∧ b = 1 ∧ c = 7 ∧ d = 7) ∨
    (a = 1 ∧ b = 5 ∧ c = 5 ∧ d = 5) := by
  unfold OrderPart at *
  omega

theorem component_orders17 {a b c : Nat}
    (ha : OrderPart a) (hb : OrderPart b) (hc : OrderPart c)
    (hab : a ≤ b) (hbc : b ≤ c) (hs : a + b + c = 17) :
    (a = 1 ∧ b = 1 ∧ c = 15) ∨
    (a = 1 ∧ b = 5 ∧ c = 11) ∨
    (a = 1 ∧ b = 7 ∧ c = 9) ∨
    (a = 5 ∧ b = 5 ∧ c = 7) := by
  unfold OrderPart at *
  omega

theorem component_orders18 {a b : Nat}
    (ha : OrderPart a) (hb : OrderPart b) (hab : a ≤ b) (hs : a + b = 18) :
    (a = 1 ∧ b = 17) ∨ (a = 5 ∧ b = 13) ∨
    (a = 7 ∧ b = 11) ∨ (a = 9 ∧ b = 9) := by
  unfold OrderPart at *
  omega

theorem order18_bipartite_screen {a b : Nat}
    (ha : OrderPart a) (hb : OrderPart b) (hab : a ≤ b)
    (hs : a + b = 18) (hcap : a * b ≤ 64) : a = 1 ∧ b = 17 := by
  rcases component_orders18 ha hb hab hs with h | h | h | h
  · exact h
  · rcases h with ⟨rfl, rfl⟩; omega
  · rcases h with ⟨rfl, rfl⟩; omega
  · rcases h with ⟨rfl, rfl⟩; omega

/-- Numerical witnesses for the eight complement rows of Section 4.
The graph-theoretic extraction of one of these witnesses remains an input. -/
inductive SmallComplementProfile : Nat → Nat → Prop where
  | n16a (m w : Nat) (hw : w + 3 ≤ 8)
      (he : 120 ≤ m + 13 * w / 2) : SmallComplementProfile 16 m
  | n16b (m u v : Nat) (hu : u ≤ 2) (hv : v ≤ 4)
      (he : 120 ≤ m + 5 * u / 2 + 9 * v / 2) : SmallComplementProfile 16 m
  | n16c (m u v : Nat) (hu : u ≤ 3) (hv : v ≤ 3)
      (he : 120 ≤ m + 7 * u / 2 + 7 * v / 2) : SmallComplementProfile 16 m
  | n16d (m u v w : Nat) (hu : u ≤ 2) (hv : v ≤ 2) (hw : w ≤ 2)
      (he : 120 ≤ m + 5 * u / 2 + 5 * v / 2 + 5 * w / 2) : SmallComplementProfile 16 m
  | n17a (m w : Nat) (hw : w + 2 ≤ 8)
      (he : 136 ≤ m + 15 * w / 2) : SmallComplementProfile 17 m
  | n17b (m u v : Nat) (hu : u ≤ 2) (hv : v ≤ 5)
      (he : 136 ≤ m + 5 * u / 2 + 11 * v / 2) : SmallComplementProfile 17 m
  | n17c (m u v : Nat) (hu : u ≤ 3) (hv : v ≤ 4)
      (he : 136 ≤ m + 7 * u / 2 + 9 * v / 2) : SmallComplementProfile 17 m
  | n17d (m u v w : Nat) (hu : u ≤ 2) (hv : v ≤ 2) (hw : w ≤ 3)
      (he : 136 ≤ m + 5 * u / 2 + 5 * v / 2 + 7 * w / 2) : SmallComplementProfile 17 m

theorem complement_profile_exceeds_budget {n m : Nat}
    (h : SmallComplementProfile n m) : biplanarBudget n < m := by
  cases h <;> unfold biplanarBudget <;> omega

theorem dense17_edge_interval {h f : Nat}
    (htotal : h + f = 136) (hcone : h + 17 ≤ 96) (hdegree : 2 * f ≤ 17 * 7) :
    57 ≤ f ∧ f ≤ 59 := by omega

theorem triangle_free_65_contradiction {m : Nat}
    (hlo : 65 ≤ m) (hhi : m ≤ 4 * 18 - 8) : False := by omega

theorem critical6_triple_table :
    [18 + gallaiBound 6 8 + 3 * 2 - chooseTwo 2,
     18 + gallaiBound 6 9 + 3 * 1 - chooseTwo 1,
     18 + gallaiBound 6 10] = [46, 47, 46] := by decide

theorem proper_critical7_table :
    [gallaiBound 7 9 + 6 * 4 - chooseTwo 4,
     gallaiBound 7 10 + 6 * 3 - chooseTwo 3,
     gallaiBound 7 11 + 6 * 2 - chooseTwo 2,
     gallaiBound 7 12 + 6] = [49, 50, 49, 46] := by decide

/-! ## List-coloring the diamond (Section 6) -/

def Distinct3 {α : Type} (A : Fin 3 → α) : Prop :=
  A 0 ≠ A 1 ∧ A 0 ≠ A 2 ∧ A 1 ≠ A 2

private theorem three_values_avoid_two {α : Type} (a b c x y : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z, (z = a ∨ z = b ∨ z = c) ∧ z ≠ x ∧ z ≠ y := by
  classical
  by_cases hax : a = x
  · subst x
    by_cases hby : b = y
    · subst y
      exact ⟨c, Or.inr (Or.inr rfl), Ne.symm hac, Ne.symm hbc⟩
    · exact ⟨b, Or.inr (Or.inl rfl), Ne.symm hab, hby⟩
  · by_cases hay : a = y
    · subst y
      by_cases hbx : b = x
      · subst x
        exact ⟨c, Or.inr (Or.inr rfl), Ne.symm hbc, Ne.symm hac⟩
      · exact ⟨b, Or.inr (Or.inl rfl), hbx, Ne.symm hab⟩
    · exact ⟨a, Or.inl rfl, hax, hay⟩

private theorem three_avoid_two {α : Type} (A : Fin 3 → α)
    (hA : Distinct3 A) (x y : α) : ∃ i, A i ≠ x ∧ A i ≠ y := by
  rcases three_values_avoid_two (A 0) (A 1) (A 2) x y hA.1 hA.2.1 hA.2.2 with
    ⟨z, hz, hx, hy⟩
  rcases hz with hz | hz | hz
  · subst z; exact ⟨0, hx, hy⟩
  · subst z; exact ⟨1, hx, hy⟩
  · subst z; exact ⟨2, hx, hy⟩

private theorem four_indices_repeat (i j k l : Fin 3) :
    i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l := by
  have checked : ∀ a b c d : Fin 3,
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by decide
  exact checked i j k l

private theorem hit_of_not_avoids {α : Type} (A : Fin 3 → α) (p : α)
    (h : ¬ (∀ i, A i ≠ p)) : ∃ i, A i = p := by
  apply Classical.byContradiction
  intro hn
  apply h
  intro i hi
  exact hn ⟨i, hi⟩

private theorem four_have_outside {α : Type} (A : Fin 3 → α) (p q r s : α)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (∀ i, A i ≠ p) ∨ (∀ i, A i ≠ q) ∨
    (∀ i, A i ≠ r) ∨ (∀ i, A i ≠ s) := by
  classical
  by_cases hp : ∀ i, A i ≠ p
  · exact Or.inl hp
  by_cases hq : ∀ i, A i ≠ q
  · exact Or.inr (Or.inl hq)
  by_cases hr : ∀ i, A i ≠ r
  · exact Or.inr (Or.inr (Or.inl hr))
  by_cases hs : ∀ i, A i ≠ s
  · exact Or.inr (Or.inr (Or.inr hs))
  rcases hit_of_not_avoids A p hp with ⟨i, hi⟩
  rcases hit_of_not_avoids A q hq with ⟨j, hj⟩
  rcases hit_of_not_avoids A r hr with ⟨k, hk⟩
  rcases hit_of_not_avoids A s hs with ⟨l, hl⟩
  exfalso
  rcases four_indices_repeat i j k l with h | h | h | h | h | h
  · exact hpq (hi.symm.trans ((congrArg A h).trans hj))
  · exact hpr (hi.symm.trans ((congrArg A h).trans hk))
  · exact hps (hi.symm.trans ((congrArg A h).trans hl))
  · exact hqr (hj.symm.trans ((congrArg A h).trans hk))
  · exact hqs (hj.symm.trans ((congrArg A h).trans hl))
  · exact hrs (hk.symm.trans ((congrArg A h).trans hl))

private theorem centers_of_outside {α : Type} (A B : Fin 3 → α)
    (hA : Distinct3 A) (hB : Distinct3 B) (p q : α)
    (hp : ∀ i, A i ≠ p) :
    ∃ a b, A a ≠ B b ∧ A a ≠ p ∧ A a ≠ q ∧ B b ≠ p ∧ B b ≠ q := by
  rcases three_avoid_two B hB p q with ⟨b, hbp, hbq⟩
  rcases three_avoid_two A hA q (B b) with ⟨a, haq, hab⟩
  exact ⟨a, b, hab, hp a, haq, hbp, hbq⟩

/-- Every diamond has a list-coloring when center lists contain three distinct
colors and tip lists contain two distinct colors. The graph-criticality bridge
from degree lists to this statement is still an explicit input below. -/
theorem diamond_lists_colorable {α : Type} (A B : Fin 3 → α) (C D : Fin 2 → α)
    (hA : Distinct3 A) (hB : Distinct3 B) (hC : C 0 ≠ C 1) (hD : D 0 ≠ D 1) :
    ∃ a b : Fin 3, ∃ p q : Fin 2,
      A a ≠ B b ∧ A a ≠ C p ∧ A a ≠ D q ∧ B b ≠ C p ∧ B b ≠ D q := by
  classical
  by_cases common : ∃ p q, C p = D q
  · rcases common with ⟨p, q, hpq⟩
    rcases three_avoid_two A hA (C p) (C p) with ⟨a, ha, _⟩
    rcases three_avoid_two B hB (C p) (A a) with ⟨b, hb, hba⟩
    refine ⟨a, b, p, q, Ne.symm hba, ha, ?_, hb, ?_⟩
    · simpa [← hpq] using ha
    · simpa [← hpq] using hb
  · have h00 : C 0 ≠ D 0 := fun h => common ⟨0, 0, h⟩
    have h01 : C 0 ≠ D 1 := fun h => common ⟨0, 1, h⟩
    have h10 : C 1 ≠ D 0 := fun h => common ⟨1, 0, h⟩
    have h11 : C 1 ≠ D 1 := fun h => common ⟨1, 1, h⟩
    rcases four_have_outside A (C 0) (C 1) (D 0) (D 1)
      hC h00 h01 h10 h11 hD with h | h | h | h
    · rcases centers_of_outside A B hA hB (C 0) (D 0) h with ⟨a, b, hh⟩
      exact ⟨a, b, 0, 0, hh⟩
    · rcases centers_of_outside A B hA hB (C 1) (D 0) h with ⟨a, b, hh⟩
      exact ⟨a, b, 1, 0, hh⟩
    · rcases centers_of_outside A B hA hB (D 0) (C 0) h with
        ⟨a, b, hab, had, hac, hbd, hbc⟩
      exact ⟨a, b, 0, 0, hab, hac, had, hbc, hbd⟩
    · rcases centers_of_outside A B hA hB (D 1) (C 0) h with
        ⟨a, b, hab, had, hac, hbd, hbc⟩
      exact ⟨a, b, 0, 1, hab, hac, had, hbc, hbd⟩

/-! ## Independent-set attachment colorings and valid cuts -/

abbrev Attachment := Fin 3 → Fin 13 → Bool

def AttachmentColorable (H : Graph 13) (x : Attachment) (k : Nat) : Prop :=
  ∃ c : Fin 13 → Fin k, ∃ d : Fin 3 → Fin k,
    Proper H c ∧ ∀ i v, x i v = true → d i ≠ c v

def Blocks {k : Nat} (x : Attachment) (c : Fin 13 → Fin k) (i : Fin 3) : Prop :=
  ∀ color : Fin k, ∃ v, x i v = true ∧ c v = color

/-- The quantified color-class cut (15), including the same-color choices on
multiple new vertices: those vertices have no edges between them. -/
theorem attachment_cut_sound {k : Nat} (H : Graph 13) (x : Attachment)
    (c : Fin 13 → Fin k) (hc : Proper H c)
    (hbad : ¬ AttachmentColorable H x k) : ∃ i, Blocks x c i := by
  classical
  apply Classical.byContradiction
  intro hnone
  have missing : ∀ i : Fin 3, ∃ color : Fin k,
      ∀ v, x i v = true → c v ≠ color := by
    intro i
    apply Classical.byContradiction
    intro hmissing
    apply hnone
    refine ⟨i, ?_⟩
    intro color
    apply Classical.byContradiction
    intro hhit
    apply hmissing
    refine ⟨color, ?_⟩
    intro v hx heq
    exact hhit ⟨v, hx, heq⟩
  apply hbad
  refine ⟨c, (fun i => Classical.choose (missing i)), hc, ?_⟩
  intro i v hx
  exact Ne.symm (Classical.choose_spec (missing i) v hx)

/-- Literal degree, size, and clique constraints used in the ten attachment models. -/
def AttachmentConstraints (H : Graph 13) (x : Attachment) : Prop :=
  edgeCount H + sumFin 3 (fun i => sumFin 13 (fun v => if x i v then 1 else 0)) ≤ 63 ∧
  (∀ i, 7 ≤ sumFin 13 (fun v => if x i v then 1 else 0)) ∧
  (∀ v, 7 ≤ degree H v + sumFin 3 (fun i => if x i v then 1 else 0)) ∧
  CliqueFree H 7 ∧
  (∀ i (f : Fin 6 → Fin 13), Injective f →
    (∀ a b, a ≠ b → Adj H (f a) (f b)) → ∃ j, x i (f j) = false)

/-! ## Literal graphs: the four bases and the order-18 density certificate -/

private def baseMasks (i : Fin 4) : List Nat :=
  match i.val with
  | 0 => [252, 8184, 7937, 243, 235, 219, 187, 123, 7686, 7430, 6918, 5894, 3846]
  | 1 => [508, 8176, 7689, 7685, 483, 467, 435, 371, 243, 7182, 6670, 5646, 3598]
  | 2 => [1020, 8160, 7193, 7189, 7181, 963, 931, 867, 739, 483, 6174, 5150, 3102]
  | _ => [2040, 8068, 8066, 6257, 6249, 6233, 6201, 1799, 1671, 1415, 903, 4222, 2174]

private def baseEdge (i : Fin 4) (u v : Fin 13) : Bool :=
  Nat.testBit ((baseMasks i).getD u.val 0) v.val

def canonicalBase (i : Fin 4) : Graph 13 where
  edge := baseEdge i
  symm := (by decide : ∀ j : Fin 4, ∀ u v : Fin 13, baseEdge j u v = baseEdge j v u) i
  loopless := (by decide : ∀ j : Fin 4, ∀ u : Fin 13, baseEdge j u u = false) i

private def baseColorList (i : Fin 4) : List Nat :=
  match i.val with
  | 0 => [0, 1, 1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2]
  | 1 => [0, 1, 2, 1, 3, 4, 5, 6, 2, 6, 5, 4, 3]
  | 2 => [0, 1, 2, 3, 1, 4, 5, 6, 3, 2, 6, 5, 4]
  | _ => [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 3, 6, 5]

def canonicalBaseColor (i : Fin 4) (v : Fin 13) : Fin 7 :=
  ⟨(baseColorList i).getD v.val 0,
   (by decide : ∀ j : Fin 4, ∀ u : Fin 13, (baseColorList j).getD u.val 0 < 7) i v⟩

theorem canonical_bases_colored (i : Fin 4) : Colorable (canonicalBase i) 7 := by
  refine ⟨canonicalBaseColor i, ?_⟩
  have checked : ∀ j : Fin 4, Proper (canonicalBase j) (canonicalBaseColor j) := by
    unfold Proper Adj
    decide
  exact checked i

theorem canonical_base_edge_counts :
    [edgeCount (canonicalBase 0), edgeCount (canonicalBase 1),
     edgeCount (canonicalBase 2), edgeCount (canonicalBase 3)] = [41, 41, 41, 42] := by decide

theorem canonical_bases_no_independent_triple :
    ∀ i : Fin 4, ¬ IndependentTriple (canonicalBase i) := by
  unfold IndependentTriple Adj
  decide

private def coneMasks : List Nat :=
  [147214, 147213, 147211, 147207, 260320, 260304, 260272, 260208, 247311, 247055, 246543, 143615, 141567, 137471, 231408, 215024, 182256, 131071]

private def obstructionMasks : List Nat :=
  [147200, 147200, 147200, 147200, 260096, 260096, 260096, 260096, 114703, 114703, 114703, 255, 255, 255, 2032, 2032, 2032, 255]


private def maskEdge18 (rows : List Nat) (u v : Fin 18) : Bool :=
  Nat.testBit (rows.getD u.val 0) v.val

def canonicalCone : Graph 18 where
  edge := maskEdge18 coneMasks
  symm := by decide
  loopless := by decide

def dense17Obstruction : Graph 18 where
  edge := maskEdge18 obstructionMasks
  symm := by decide
  loopless := by decide

theorem dense17_obstruction_edges : edgeCount dense17Obstruction = 65 := by decide

theorem dense17_obstruction_triangle_free : TriangleFree dense17Obstruction := by
  unfold TriangleFree Adj
  decide

theorem dense17_obstruction_contained : Contains dense17Obstruction canonicalCone := by
  unfold Contains Adj
  decide

/-! ## Exact statements of the remaining graph-level obligations -/

/-- An actual critical subgraph disjoint from an actual independent triple.
This witness is essential: an integer t satisfying an edge inequality alone
would not justify either structural attachment reduction. -/
def CriticalCoreOffTriple {n : Nat} (G : Graph n) (t : Nat) : Prop :=
  ∃ a : Fin 3 → Fin n,
    Injective a ∧ (∀ i j, i ≠ j → ¬ Adj G (a i) (a j)) ∧
    ∃ Q : Graph t, Critical Q 9 ∧
      ∃ f : Embedding Q G, ∀ u i, f.map u ≠ a i

/-- Tips have labels 0,1 and centers labels 2,3. -/
def LowDegreeDiamond {n : Nat} (G : Graph n) (d : Nat) : Prop :=
  ∃ f : Fin 4 → Fin n,
    Injective f ∧
    (∀ i j, Adj G (f i) (f j) ↔ i ≠ j ∧ (2 ≤ i.val ∨ 2 ≤ j.val)) ∧
    (∀ i, degree G (f i) = d)

def Dense17 (F : Graph 17) : Prop :=
  MaximalTriangleFree F ∧ AlphaAtMost F 7 ∧
  (∀ v, degree F v ≤ 7) ∧ 57 ≤ edgeCount F ∧ edgeCount F ≤ 59

/-- G is a cone over the complement of F, without assuming a particular labeling. -/
def ConeComplement (F : Graph 17) (G : Graph 18) : Prop :=
  ∃ f : Fin 17 → Fin 18, ∃ apex : Fin 18,
    Injective f ∧ (∀ u, f u ≠ apex) ∧
    (∀ u, Adj G apex (f u)) ∧
    (∀ u v, u ≠ v → (Adj G (f u) (f v) ↔ ¬ Adj F u v)) ∧
    (∀ v, v = apex ∨ ∃ u, v = f u)

def KnownBase (R : Graph 13) : Prop :=
  ∃ i : Fin 4, Isomorphic R (canonicalBase i)

def AdmissibleBase (H : Graph 13) : Prop :=
  ∃ R : Graph 13,
    Critical R 7 ∧ CliqueFree R 7 ∧ edgeCount R ≤ 42 ∧
    Contains R H ∧ edgeCount H ≤ 42 ∧ edgeCount H ≤ edgeCount R + 1

def CatalogueAugmentation (H : Graph 13) : Prop :=
  ∃ R : Graph 13, KnownBase R ∧ Contains R H ∧
    edgeCount H ≤ 42 ∧ edgeCount H ≤ edgeCount R + 1

/-- These are proof obligations, not imported facts. Several fields include
new reductions from the manuscript, not only previously published theorems. -/
structure GraphReductionInputs (P : PlanarPredicate) : Prop where
  criticalExtraction : ∀ {n : Nat} (G : Graph n),
    Biplanar P G → ¬ Colorable G 9 →
    ∃ m : Nat, ∃ H : Graph m, m ≤ n ∧ Biplanar P H ∧ Critical H 10
  minimumOrder : ∀ {n : Nat} (G : Graph n),
    Biplanar P G → Critical G 10 → 12 ≤ n
  eulerBound : ∀ {n : Nat} (G : Graph n),
    Biplanar P G → 3 ≤ n → edgeCount G ≤ biplanarBudget n
  triangleFreeSubgraphBound : ∀ {n : Nat} (G S : Graph n),
    Biplanar P G → 3 ≤ n → Contains S G → TriangleFree S → edgeCount S ≤ 4 * n - 8
  gallai10 : ∀ {n : Nat} (G : Graph n),
    Critical G 10 → 12 ≤ n → n ≤ 18 → gallaiBound 10 n ≤ edgeCount G
  tripleCore : ∀ {n : Nat} (G : Graph n),
    Biplanar P G → Critical G 10 → 16 ≤ n → n ≤ 18 → IndependentTriple G →
    ∃ t : Nat, 11 ≤ t ∧ t ≤ n - 3 ∧ CriticalCoreOffTriple G t ∧
      tripleBound n t ≤ edgeCount G
  smallComplementProfile : ∀ {n : Nat} (G : Graph n),
    Biplanar P G → Critical G 10 → 16 ≤ n → n ≤ 17 →
    ¬ IndependentTriple G → SmallComplementProfile n (edgeCount G)
  dense17Reduction : ∀ (G : Graph 18),
    Biplanar P G → Critical G 10 → ¬ IndependentTriple G →
    ∃ F : Graph 17, Dense17 F ∧ ConeComplement F G
  diamondCriticalBridge : ∀ {n : Nat} (G : Graph n),
    Critical G 10 → ¬ LowDegreeDiamond G 9
  t11Diamond : ∀ (G : Graph 18),
    Biplanar P G → Critical G 10 → CriticalCoreOffTriple G 11 → LowDegreeDiamond G 9
  t15Attachment : ∀ (G : Graph 18),
    Biplanar P G → Critical G 10 → CriticalCoreOffTriple G 15 →
    ∃ H : Graph 13, ∃ x : Attachment,
      AdmissibleBase H ∧ AttachmentConstraints H x ∧ ¬ AttachmentColorable H x 7

/-- The finite classifications and attachment exclusions remain unproved in
Lean. External enumeration and MILP checks establish the manuscript's
computer-assisted evidence, but do not instantiate this structure. -/
structure FiniteCaseInputs : Prop where
  dense17Certificate : ∀ (F : Graph 17) (G : Graph 18),
    Dense17 F → ConeComplement F G →
    ∃ S : Graph 18, Contains S G ∧ TriangleFree S ∧ 65 ≤ edgeCount S
  bases13Complete : ∀ (R : Graph 13),
    Critical R 7 → CliqueFree R 7 → edgeCount R ≤ 42 → KnownBase R
  attachmentsColorable : ∀ (H : Graph 13) (x : Attachment),
    CatalogueAugmentation H → AttachmentConstraints H x → AttachmentColorable H x 7

/-! ## Conditional theorem assembly -/

theorem no_critical_through17 (P : PlanarPredicate) (T : GraphReductionInputs P)
    {n : Nat} (G : Graph n) (hn : n ≤ 17)
    (hb : Biplanar P G) (hc : Critical G 10) : False := by
  have hlo : 12 ≤ n := T.minimumOrder G hb hc
  have hcap : edgeCount G ≤ biplanarBudget n := T.eulerBound G hb (by omega)
  by_cases hs : n ≤ 15
  · exact small_order_arithmetic hlo hs
      (T.gallai10 G hc hlo (by omega)) hcap
  · have hn₁ : 16 ≤ n := by omega
    by_cases hi : IndependentTriple G
    · rcases T.tripleCore G hb hc hn₁ (by omega) hi with ⟨t, ht₁, ht₂, _, ht⟩
      have hgap := triple_exceeds_budget_before18 hn₁ hn ht₁ ht₂
      omega
    · have hp := T.smallComplementProfile G hb hc hn₁ hn hi
      have hgap := complement_profile_exceeds_budget hp
      omega

theorem no_critical_order18 (P : PlanarPredicate) (T : GraphReductionInputs P)
    (F : FiniteCaseInputs) (G : Graph 18)
    (hb : Biplanar P G) (hc : Critical G 10) : False := by
  have hcap : edgeCount G ≤ 96 := by
    simpa [biplanarBudget] using T.eulerBound G hb (by decide : 3 ≤ 18)
  by_cases hi : IndependentTriple G
  · rcases T.tripleCore G hb hc (by decide) (by decide) hi with
      ⟨t, ht₁, ht₂, hcore, ht⟩
    have hcases : t = 11 ∨ t = 15 := order18_triple_cases ht₁ ht₂ ht hcap
    rcases hcases with h11 | h15
    · subst t
      exact T.diamondCriticalBridge G hc (T.t11Diamond G hb hc hcore)
    · subst t
      rcases T.t15Attachment G hb hc hcore with ⟨H, x, hbase, hx, hbad⟩
      rcases hbase with ⟨R, hR, hK, hE, hRH, hH42, hHplus⟩
      have hknown : KnownBase R := F.bases13Complete R hR hK hE
      have hcat : CatalogueAugmentation H := ⟨R, hknown, hRH, hH42, hHplus⟩
      exact hbad (F.attachmentsColorable H x hcat hx)
  · rcases T.dense17Reduction G hb hc hi with ⟨D, hD, hcone⟩
    rcases F.dense17Certificate D G hD hcone with ⟨S, hSG, htri, h65⟩
    have h64 := T.triangleFreeSubgraphBound G S hb (by decide : 3 ≤ 18) hSG htri
    exact triangle_free_65_contradiction h65 h64

/-- Main assembly theorem. It is explicitly CONDITIONAL: `T` and `F` are
not constructed in this project. The result is not an unconditional Lean
formalization of the graph theorem in the manuscript. -/
theorem nine_colorable_through18_of_inputs
    (P : PlanarPredicate) (T : GraphReductionInputs P) (F : FiniteCaseInputs)
    {n : Nat} (G : Graph n) (hn : n ≤ 18) (hb : Biplanar P G) : Colorable G 9 := by
  apply Classical.byContradiction
  intro hbad
  rcases T.criticalExtraction G hb hbad with ⟨m, H, hmn, hH, hc⟩
  by_cases hm : m ≤ 17
  · exact no_critical_through17 P T H hm hH hc
  · have hm18 : m = 18 := by omega
    subst m
    exact no_critical_order18 P T F H hH hc

#print axioms diamond_lists_colorable
#print axioms dense17_obstruction_triangle_free
#print axioms nine_colorable_through18_of_inputs

end EarthMoon
