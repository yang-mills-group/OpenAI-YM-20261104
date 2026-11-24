import YM.Integration.WilsonCapturedPrimaryWindingVerseRoster

/-! Occupied and quiet entries of the same finite marked Gaussian integrand. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingVerseDeposit
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonVacuumPreResetFiniteRegister WilsonOriginalSingleMarkedRegister WilsonOriginalMixedGaussianTable
open WilsonCapturedPrimaryWindingVerseRoster
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {V ι S : Type} [Fintype V] [DecidableEq V] [Fintype ι] (J : Census V) (r : ℕ)
variable (x : S → ℝ) (P : Ink S) (badge : ι → J.Mode) (c : ι → ℂ) (T : ι → Ink S)

def written : Grade J r := register J r (observed x P) + ∑ l, mark J r x badge c T l

def entry (t : J.Mode) (b : Index r) : ℂ :=
  (b.val.card.factorial : ℂ) * (if t.val.Nonempty then
    ∑ l, if badge l = t then c l * ↑(MvPolynomial.eval x (coeff b.val.card (T l))) else 0
    else ↑(MvPolynomial.eval x (coeff b.val.card P)))

theorem face (hot : ∀ l, (badge l).val.Nonempty) (t : J.Mode) (b : Index r) :
    (written J r x P badge c T).part (Join.pair t b) = entry J r x P badge c T t b := by
  have each (l : ι) : (mark J r x badge c T l).part (Join.pair t b) =
      (b.val.card.factorial : ℂ) * (if badge l = t then
        c l * ↑(MvPolynomial.eval x (coeff b.val.card (T l))) else 0) := by
    rw [mark,term_value,coefficient,Poly.part_smul,Poly.part_send]
    by_cases h : badge l = t
    · subst t; simp; ring
    · simp [h,Ne.symm h]
  rw [written,Poly.part_plus,Poly.part_sum,WilsonVacuumPreResetFiniteRegister.read]
  simp only [each,← Finset.mul_sum,entry]
  by_cases h : t.val.Nonempty
  · rw [if_pos h,if_neg ((hot_iff_ne _).1 h),mul_zero,zero_add]
  · have hq : t = J.quiet := of_not_not (mt (hot_iff_ne _).2 h)
    subst t
    have skip (l : ι) : badge l ≠ J.quiet := (hot_iff_ne _).1 (hot l)
    simp [skip,h,OriginalRadialSeries.observed]

theorem quiet (z : constantCoeff P = 0) (hot : ∀ l, (badge l).val.Nonempty) :
    (written J r x P badge c T).part (Board J r).quiet = 0 := by
  rw [← Join.pair_quiet,face J r x P badge c T hot,entry]
  rw [if_neg (show ¬ J.quiet.val.Nonempty from Finset.not_nonempty_empty)]
  change ((_ : ℕ).factorial : ℂ) * ↑(MvPolynomial.eval x (coeff 0 P)) = 0
  rw [coeff_zero_eq_constantCoeff_apply,z,map_zero]; simp

theorem received
    (h : Hot (Board J r) → ℂ) (z : constantCoeff P = 0) (hot : ∀ l, (badge l).val.Nonempty)
    (matchRow : ∀ s, h s = entry J r x P badge c T (Join.left s.val) (Join.right s.val)) :
    Poly.pass (lit (Board J r) h) =
      stock J r x (fun b : Finset ι => ∏ l ∈ b, coefficient J badge c l)
        (fun b => raiseE P * ∏ l ∈ b, T l) := by
  have logged : lit (Board J r) h = written J r x P badge c T := by
    apply Join.both_parts
    intro t b
    by_cases hs : (Join.pair t b).val.Nonempty
    · rw [part_lit _ ⟨_,hs⟩,matchRow,Join.left_pair,Join.right_pair,face J r x P badge c T hot]
    · have hq : Join.pair t b=(Board J r).quiet := of_not_not (mt (hot_iff_ne _).2 hs)
      rw [hq,part_lit_quiet,quiet J r x P badge c T z hot]
  rw [logged]
  exact expanded J r x badge c T P z hot

end YM.Integration.WilsonCapturedPrimaryWindingVerseDeposit
