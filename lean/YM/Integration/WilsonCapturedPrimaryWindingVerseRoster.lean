import YM.Integration.WilsonOriginalJointGaussianIncome

/-! Polarization of a finite filed roster before taking its Gaussian expectation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingVerseRoster
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open Extra.Trajectories (pass_add pass_zero)
open WilsonVacuumPreResetFiniteRegister WilsonOriginalSingleMarkedRegister WilsonOriginalMixedGaussianTable
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
open private multiplied absent from YM.Integration.WilsonOriginalJointGaussianIncome
variable {V ι S : Type} [Fintype V] [DecidableEq V] (J : Census V) (r : ℕ)
variable (x : S → ℝ) (badge : ι → J.Mode) (c : ι → ℂ) (T : ι → Ink S)

def coefficient (l : ι) : Poly J := c l • Poly.send (badge l) 1

def mark (l : ι) : Grade J r :=
  term J r x (coefficient J badge c l) (T l)

private theorem mounted (l : ι) : mark J r x badge c T l =
    token J r (badge l) * (c l • register J r (observed x (T l))) := by
  simp only [mark,term,coefficient,token,map_smul,smul_mul_assoc,mul_smul_comm]

private theorem mark_quiet (l : ι) (hot : (badge l).val.Nonempty) :
    (mark J r x badge c T l).part (Board J r).quiet = 0 := by
  rw [mounted]
  exact absent J r _ hot _

private theorem mark_pass (l : ι) (hot : (badge l).val.Nonempty) :
    Poly.pass (mark J r x badge c T l) = 1 + mark J r x badge c T l := by
  rw [mounted]
  have zero : register J r (raiseE (0 : PowerSeries ℝ)) = 1 := by
    rw [WilsonVacuumPreResetFiniteRegister.exponential J r 0 (by simp),map_zero,pass_zero]
  simpa only [map_zero,zero_add,zero,one_mul] using
    (WilsonOriginalSingleMarkedRegister.exponential J r (badge l) hot
      (c l • register J r (observed x (T l))) 0 (by simp))

private theorem quiet_sum (L : Finset ι) (hot : ∀ l, (badge l).val.Nonempty) :
    (∑ l ∈ L, mark J r x badge c T l).part (Board J r).quiet = 0 := by
  simp only [Poly.part_sum,mark_quiet J r x badge c T _ (hot _),sum_const_zero]

private theorem marked_product (L : Finset ι) (hot : ∀ l, (badge l).val.Nonempty) :
    Poly.pass (∑ l ∈ L, mark J r x badge c T l) =
      ∏ l ∈ L, (mark J r x badge c T l + 1) := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert l L absent previous =>
    rw [sum_insert absent,prod_insert absent,pass_add (mark_quiet J r x badge c T l (hot l))
      (quiet_sum J r x badge c T L hot),mark_pass J r x badge c T l (hot l),previous,add_comm]

private theorem coupled (I : Finset ι) :
    ∏ l ∈ I, mark J r x badge c T l =
      term J r x (∏ l ∈ I, coefficient J badge c l) (∏ l ∈ I, T l) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [term]
  | @insert l I absent previous =>
    rw [prod_insert absent,prod_insert absent,prod_insert absent,previous]
    exact multiplied J r x _ _ _ _

theorem expanded [Fintype ι] (φ : Ink S) (z : constantCoeff φ = 0)
    (hot : ∀ l, (badge l).val.Nonempty) :
    Poly.pass (register J r (observed x φ) + ∑ l, mark J r x badge c T l) =
      stock J r x (fun b : Finset ι => ∏ l ∈ b, coefficient J badge c l)
        (fun b => raiseE φ * ∏ l ∈ b, T l) := by
  classical
  have zobs : constantCoeff (observed x φ) = 0 := by
    change MvPolynomial.eval x (constantCoeff φ) = 0
    rw [z,map_zero]
  have quiet : (register J r (observed x φ)).part (Board J r).quiet = 0 := by
    rw [← Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
    change ((_ : ℕ).factorial : ℂ) * ↑(coeff 0 (observed x φ)) = 0
    rw [coeff_zero_eq_constantCoeff_apply,zobs]; simp
  have zeroX : constantCoeff (observed x PowerSeries.X) = 0 := by
    simp [OriginalRadialSeries.observed]
  have exp := raise_map (observed x) zeroX z
  have vac : register J r (observed x (raiseE φ)) = term J r x 1 (raiseE φ) := by
    simp [term]
  rw [pass_add quiet (quiet_sum J r x badge c T univ hot),
    ← WilsonVacuumPreResetFiniteRegister.exponential J r _ zobs,← exp,vac,
    marked_product J r x badge c T univ hot,Fintype.prod_add]
  simp only [prod_const_one,mul_one]
  rw [Finset.mul_sum]
  unfold stock
  apply sum_congr rfl
  intro b _
  rw [coupled,multiplied,one_mul]

end YM.Integration.WilsonCapturedPrimaryWindingVerseRoster
