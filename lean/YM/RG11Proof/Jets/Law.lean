import YM.RG11Proof.Jets.Matrix
/-!
# Formal filtration/reality frames (finite field horizon)

Positive coefficient constraints given by a multiplication-closed submodule
of matrices (e.g. real unit-annihilating signed-symmetry intertwiners
preserving an engineering filtration). Inverse preserves these constraints; no
representation-dependent estimates needed for that FORMAL assertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries
open scoped BigOperators

variable {J R : Type*}

/-- Homogeneous variation constraints, model independent. -/
structure Constraints (R J : Type*) [CommRing R] [Fintype J] where
  vary : Submodule R (Square J R)
  both {A B} : A ∈ vary → B ∈ vary → A*B ∈ vary

namespace Constraints
variable [CommRing R] [Fintype J]
variable (L : Constraints R J)

def Full : Constraints R J := ⟨⊤, fun _ _ => Submodule.mem_top ⟩

def inf (M : Constraints R J) : Constraints R J where
  vary := L.vary ⊓ M.vary
  both h k := ⟨L.both h.1 k.1, M.both h.2 k.2⟩

/-- E labels real homogeneous basis; connecting entries may lower, never raise. -/
def filter (grade : J→ℕ) : Constraints R J where
  vary := {
    carrier := {A | Matrix.BlockTriangular A (OrderDual.toDual ∘ grade)}
    zero_mem' := Matrix.blockTriangular_zero
    add_mem' := Matrix.BlockTriangular.add
    smul_mem' := fun t A (h:Matrix.BlockTriangular _ _) i j hij=> by
      rw [Matrix.smul_apply,h hij,smul_zero]
  }
  both := Matrix.BlockTriangular.mul

/-- For already mass-independent separated answers require preservation of each grade. -/
def sameGrade (grade : J→ℕ) : Constraints R J :=
  (filter grade).inf {
    vary := {
      carrier := {A | Matrix.BlockTriangular A grade}
      zero_mem' := Matrix.blockTriangular_zero
      add_mem' := Matrix.BlockTriangular.add
      smul_mem' := fun t A (h: Matrix.BlockTriangular _ _) i j hij=> by
        rw [Matrix.smul_apply,h hij,smul_zero]
    }
    both := Matrix.BlockTriangular.mul }

/-- Kill unit, not its column: incoming higher fields can map to identity. -/
def unitAt (u : J) : Constraints R J where
  vary := {
    carrier := {A | ∀ j, A u j = 0}
    zero_mem' := fun _ => rfl
    add_mem' {x y} h j k := by rw [Matrix.add_apply,h,j,add_zero]
    smul_mem' t x h k := by rw [Matrix.smul_apply,h,smul_zero] }
  both {A B} h _ j := by rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _=> by rw [h k,zero_mul]

/-- Commute with every matrix in a symmetry list (finite or not). -/
def actions {I : Type*} (H : I→ Square J R) : Constraints R J where
  vary := {
    carrier := {A | ∀ i, A*H i= H i*A}
    zero_mem' := fun _=>by rw [zero_mul,mul_zero]
    add_mem' {x y} h j i := by rw [add_mul,mul_add,h i,j i]
    smul_mem' t x h i := by rw [Matrix.smul_mul,Matrix.mul_smul,h i] }
  both {A B} h j i := by rw [mul_assoc,j i,←mul_assoc,h i,mul_assoc]

/-- The standard constraint in the separated sector before grade adjustment.
Reality is enforced by working over ℝ (act on the real form/E_h adapted
basis only; any complexification must respect the specified conjugation).
`H` includes reflection. Coupling parity, if desired, is separate. -/
def position {I : Type*} (u : J) (grade : J→ℕ) (H : I→ Square J R) : Constraints R J :=
  ((filter grade).inf (unitAt u)).inf (actions H)

theorem mem_position_iff {I} {u : J} {grade : J→ℕ} {H : I→ Square J R} {A : Square J R} :
    A ∈ (position u grade H).vary ↔
    (∀ i j, grade i < grade j → A i j = 0) ∧ (∀ j, A u j=0) ∧ (∀ i, A*H i=H i*A) := by
  change ((Matrix.BlockTriangular _ _) ∧ (∀ j, A u j=0)) ∧ (∀ i, _) ↔ _
  unfold Matrix.BlockTriangular
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩
    exact ⟨fun _ _ h=>@h₁ _ _ h,h₂,h₃⟩
  rintro ⟨h₁,h₂,h₃⟩
  exact ⟨⟨fun _ _ h=> h₁ _ _ h,h₂⟩,h₃⟩

variable [DecidableEq J]
structure Lawful (A : Square J R⟦X⟧) : Prop where
  baseline : nearId A
  positive {i : ℕ} : 0 < i → piece i A ∈ L.vary

-- Run this explicit for any frame that is lawful (not an actual estimate).
namespace Lawful
variable {L} {A B : Square J R⟦X⟧}

theorem id : L.Lawful (1:Square J R⟦X⟧) where
  baseline := nearId_one
  positive h := by rw [piece_one,if_neg h.ne']; exact L.vary.zero_mem

theorem mul (h : L.Lawful A) (hh : L.Lawful B) : L.Lawful (A*B) where
  baseline := h.baseline.mul hh.baseline
  positive hi := by
    rename_i i
    rw [piece_mul]
    refine Submodule.sum_mem _ (fun ⟨j,k⟩ he=>?_)
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp he
    dsimp at he ⊢
    by_cases hj:j=0
    · subst j
      have hk : 0<k := by omega
      rw [h.baseline, one_mul]; exact hh.positive hk
    by_cases hk:k=0
    · subst k
      rw [hh.baseline, mul_one]; exact h.positive (Nat.pos_of_ne_zero hj)
    exact L.both (h.positive (by omega)) (hh.positive (by omega))

theorem squareInv (h : L.Lawful A) : L.Lawful (Jets.squareInv A) where
  baseline := squareInv_base _
  positive hi := by
    rename_i i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      rw [squareInv_piece _ _ hi,trail]
      refine L.vary.neg_mem (Submodule.sum_mem _ (fun z hz=> ?_))
      split
      · exact L.vary.zero_mem
      rename_i he
      have hb := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      by_cases hd : z.2=0
      · rw [hd, squareInv_base, mul_one]; exact h.positive (by omega)
      exact L.both (h.positive (by omega)) (ih z.2 (by omega) (by omega))
end Lawful
end Constraints

section subst
variable [CommRing R] {J' : Type*} {A B : Rect J J' R⟦X⟧} {p : PowerSeries R}
/-- Recouple before a field frame transform. -/
def subs (p : PowerSeries R) (A : Rect J J' R⟦X⟧) := A.map (PowerSeries.subst p)
@[simp] theorem subs_apply (i j) : subs p A i j=PowerSeries.subst p (A i j) := rfl

theorem piece_subs (h : Anchored p) (A : Rect J J' R⟦X⟧) (n : ℕ) :
    piece n (subs p A) = ∑ k∈Finset.range (n+1), coeff n (p^k) • piece k A := by
  ext i j
  simp only [piece_apply, subs_apply, coeff_compose _ _ _ h, Matrix.sum_apply, Matrix.smul_apply]
  exact Finset.sum_congr rfl fun a _=> mul_comm ..

@[simp] theorem piece0_subs (h : Anchored p) (A : Rect J J' R⟦X⟧) :
    piece 0 (subs p A) = piece 0 A := by
  ext i j
  change coeff 0 (PowerSeries.subst p _)=_
  rw [coeff_zero_eq_constantCoeff_apply,base_compose _ _ h,piece_apply,coeff_zero_eq_constantCoeff_apply]

theorem nearId.subs [DecidableEq J] (h : Anchored p) {A : Square J R⟦X⟧} (ha : nearId A) : nearId (subs p A) :=
  (piece0_subs h A).trans ha

@[simp] theorem subs_one [DecidableEq J] (h : Anchored p) : subs p (1:Square J R⟦X⟧) = 1 := by
  ext i j n; have he : PowerSeries.subst p (1:R⟦X⟧) = (1:R⟦X⟧) := by
    rw [← coe_substAlgHom (R:=R) h.permits]; exact map_one _
  have hz : PowerSeries.subst p (0:R⟦X⟧) = (0:R⟦X⟧) := by rw [← coe_substAlgHom (R:=R) h.permits]; exact map_zero _
  by_cases hl:i=j <;> simp only [subs_apply, Matrix.one_apply, hl, ↓reduceIte,he,hz]

theorem subs_mul [Fintype J'] (h : Anchored p) {K : Type*} (A : Rect J J' R⟦X⟧) (B : Rect J' K R⟦X⟧) :
    subs p (A*B)=subs p A * subs p B := by
  ext i j n
  simp only [subs_apply,Matrix.mul_apply,← coe_substAlgHom (R:=R) h.permits,map_sum,map_mul]

theorem subs_subs (A : Rect J J' R⟦X⟧) {p q : R⟦X⟧} (ha : Anchored p) (hb : Anchored q) :
    subs q (subs p A)=subs (PowerSeries.subst q p) A := Matrix.ext fun _ _ =>
  PowerSeries.subst_comp_subst_apply (T:=R) ha.permits hb.permits _

@[simp] theorem subs_X (A : Rect J J' R⟦X⟧) : subs X A = A := Matrix.ext fun _ _ => X_subst ..

theorem MatThrough.subs {n} (hh : MatThrough n A B) {p q : PowerSeries R} (he : Through n p q) (hz : Anchored p) :
    MatThrough n (Jets.subs p A) (Jets.subs q B) := fun _ _=> Through.compose (hh _ _) he hz

theorem Constraints.Lawful.subs [Fintype J] [DecidableEq J] {L : Constraints R J}
    {A : Square J R⟦X⟧} (ha : L.Lawful A) (h : Anchored p) : L.Lawful (Jets.subs p A) where
  baseline := ha.baseline.subs h
  positive hi := by
    rename_i i
    rw [piece_subs h]
    refine Submodule.sum_mem _ (fun n _=> ?_)
    cases n with
    | zero => simp only [pow_zero,PowerSeries.coeff_one,if_neg hi.ne',zero_smul]; exact L.vary.zero_mem
    | succ n => exact L.vary.smul_mem _ (ha.positive (by omega))
end subst
end YM.RG11.Jets
