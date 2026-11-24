import YM.Integration.OriginalIssuedMarkedRows

/-! File a fresh independent source beside an already deposited Wilson marked family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonDepositedFreshMarkedInput
open Function Finset Wilson Lattice RG Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Winding
open OriginalIssuedMarkedRows FundedMarkedPathSelection IndependentSourcePathFamily
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge}
  {D k : V → ℕ} {I : V → Type} [∀ v,Fintype (I v)] {m e : ℕ} {A : ℝ}
  {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}
  (X : Input Q hm univ k D A) (hA : 0 ≤ A) (old : Finset V)
  (seeds : ∀ v, I v → Seed G (D v)) (w : Gear G → ℝ) (hw : ∀ I,0 < w I)
  (legal : ∀ v s,(seeds v s).rank ≤ k v+(seeds v s).head)

abbrev amount := A+OriginalIssuedMarkedRows.fee (k:=k) seeds Q hm w

/-- Every previously present subword is retained. New singleton subwords
are the native registered sources at their independent fine positions. -/
def posted (X : Input Q hm univ k D A) (hA : 0 ≤ A) (old : Finset V)
    (seeds : ∀ v, I v → Seed G (D v)) (w : Gear G → ℝ) (hw : ∀ I,0 < w I)
    (legal : ∀ v s,(seeds v s).rank ≤ k v+(seeds v s).head) :
    Input Q hm univ k D (amount (A:=A) (k:=k) (hm:=hm) seeds w) := by
  classical
  let Y := OriginalIssuedMarkedRows.input seeds Q hm w hw univ X.offsets legal
  have hY := (OriginalIssuedMarkedRows.enters seeds Q hm w hw univ X.offsets legal).1
  refine { familyAt := fun y J => if J ⊆ old then X.familyAt y J else Y.familyAt y J
           offsets := X.offsets
           empty := ?_
           degree := ?_
           price := ?_ }
  · intro y
    simpa using X.empty y
  · intro y J
    by_cases kept : J ⊆ old
    · simpa only [if_pos kept] using X.degree y J
    · simpa only [if_neg kept] using Y.degree y J
  · intro y J hJ i hi l
    by_cases kept : J ⊆ old
    · simpa only [if_pos kept] using (X.price y J hJ i hi l).more
        (pow_le_pow_left₀ hA (le_add_of_nonneg_right hY) J.card)
    · have priced := (Y.price y J hJ i hi l).more (pow_le_pow_left₀ hY (le_add_of_nonneg_left hA) J.card)
      rw [show Y.offsets = X.offsets by rfl] at priced
      simpa only [if_neg kept] using priced

theorem deposited (y : V → Cover) {J : Finset V} (hJ : J ⊆ old) :
    (posted X hA old seeds w hw legal).familyAt y J = X.familyAt y J := if_pos hJ

theorem fresh (y : V → Cover) {v : V} (hv : v ∉ old) :
    (posted X hA old seeds w hw legal).familyAt y {v} =
      IndependentSourcePathFamily.single seeds v (chartIn (loose Q.draws m) y (X.offsets y) v) := by
  classical
  change (if {v} ⊆ old then _ else independent seeds _ {v}) = _
  rw [if_neg (by simpa only [singleton_subset_iff] using hv),IndependentSourcePathFamily.singleton]
  rfl

/-- The mixed coefficient is generated at the next joint logarithm; an
independently filed fresh source has no mixed entry at its birth. -/
theorem mixed (y : V → Cover) {J : Finset V} (hJ : ¬J ⊆ old) (multi : ∀ v,J ≠ {v}) :
    (posted X hA old seeds w hw legal).familyAt y J = 0 := by
  classical
  change (if J ⊆ old then _ else independent seeds _ J) = 0
  rw [if_neg hJ]
  exact sum_eq_zero fun v _ => dif_neg (multi v).symm

end YM.Integration.WilsonDepositedFreshMarkedInput
