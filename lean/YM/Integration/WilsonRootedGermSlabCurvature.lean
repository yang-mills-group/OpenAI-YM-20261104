import YM.Integration.WilsonRootedGermSlabArm
import YM.Integration.WilsonMatrixOriginalGermSlabCalendar
import YM.Integration.WilsonRootedGermSparseQuota

/-! The complete earlier charged component against the independent failed
curvature response has an absolute first moment on a growing physical interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermSlabCurvature
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker MergeProof
open Spec Table FVA2 Push Push.GridApprox
open OPE.Therm MS.Local.Physical LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato ActualRunPacketRetuning MergeProof.Accent Pert.Asymptotics RG17
open WilsonInheritedRegisteredField WilsonMatrixTicketLanesReportedPivot Trace.Physical.GermGraph Next.Rank.Price
open WilsonRootedGermRegisteredSparse WilsonMatrixOriginalGermNearFields Extra.Multi.BasisCost
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
open private allocated from YM.Integration.WilsonRootedGermRegisteredSparse
open private square from YM.Integration.WilsonRootedGermSparseQuota
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple)
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (σ:ℝ)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
    (V:Ultrafilter (ℕ×ℕ)) (cut:(V:Filter (ℕ×ℕ)) ≤ L.lens)
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem column (warm:Poetry R.family.path.levels) (i:ℕ) : stock R.family i ≤ β i := by
  let P := R.family.path.levels.params i
  have bill := (warm.stage i).jobs
  change 100000*(1+P.paths+P.supportExponent+P.clip.relaxation+P.width+P.columns+P.clip.direct+P.clip.linear) ≤ Real.log (β i) at bill
  calc
    _ = P.columns := rfl
    _ ≤ Real.log (β i) := by linarith only [bill,P.paths_pos,P.price_pos,P.width_pos,P.columns_ge,P.clip.radius_pos,P.clip.quadratic_pos,P.clip.tail_pos]
    _ ≤ _ := (Real.log_le_sub_one_of_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed i))).trans (sub_le_self _ zero_le_one)

private theorem change_level {i j N p : ℕ} (eq:i=j) (w:R.family.label 4) (B:ℕ→ℝ) (hi:i≤N) (hj:j≤N)
    (h:∀(x:Site (R.family.side i p)) (U:Config G (R.family.side i p)), ‖forced R.makes hi w x U‖ ≤ B i) :
    ∀(x:Site (R.family.side j p)) (U:Config G (R.family.side j p)), ‖forced R.makes hj w x U‖ ≤ B j := by
  subst j
  exact h

def span : ℕ→ℕ := (WilsonMatrixOriginalGermSlabCalendar.growing R simple).choose

theorem tends : Tendsto (span R simple) atTop atTop :=
  (WilsonMatrixOriginalGermSlabCalendar.growing R simple).choose_spec.1

include cut in
theorem purchased (warm:Poetry R.family.path.levels) (a b q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,
      ∀ (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))),d.level=m →
      ∀ (r:ℝ),L.level r=d.level+1 → d.cutoff ≤ (d.level+1)+span R simple (d.level+1) →
      R.family.ref 4 ≤ d.level+1 → ∀ (w v:R.family.label 4) (x y:Site (R.family.side (d.level+1) d.period)),
      let k:=d.level+1
      let Z:=atRef L 4 r (d.cutoff,d.period) w
      let O:=atRef L 4 r (d.cutoff,d.period) v
      amount R k d.cutoff d.period Z ≤ β k^a → amount R k d.cutoff d.period O ≤ β k^b →
      let T:=fun U=>forced R.makes d.below Z x U*row R simple J A Q σ d O y U
      let ν:=scene R.family.path d.cutoff d.period k
      Integrable T ν ∧ (∫U,‖T U‖ ∂ν) ≤ ε*regulatorRun R.family d.cutoff d.period k^q := by
  let t:=exponent R a
  let C:=price (R.family.localSection 4)+3
  have Cp : 0<C := by have h:=price_pos (R.family.localSection 4);dsimp only [C];linarith
  let δ:=ε/(C*(2:ℝ)^t)
  have dp : 0<δ := div_pos ep (mul_pos Cp (pow_pos zero_lt_two _))
  obtain ⟨s,start⟩:=eventually_atTop.mp (WilsonMatrixOriginalGermSlabCalendar.growing R simple).choose_spec.2
  filter_upwards [eventually_ge_atTop s, WilsonInvariantActionFineFinance.original R simple Q J A σ Φ L V cut warm b 0 (q+2*t) dp] with m past fine
  intro d date r tip close age w v x y k Z O old fresh T ν
  have live : k≤d.cutoff := d.below
  have prices:=start k (by dsimp only [k];omega) d.cutoff live close
  change R.family.S.a k/R.family.S.a d.cutoff ≤ β k ∧ β d.cutoff ≤ β k^2 at prices
  have fee := (allocated R k d.cutoff d.period Z).trans (mul_le_mul_of_nonneg_left old (pow_pos (R.family.S.a_pos k) 4).le)
  have hOld : ∀ (z : Site (R.family.side k d.period)) (U : Config G (R.family.side k d.period)), ‖forced R.makes d.below Z z U‖ ≤ C*β k^t := by
    have h:=WilsonRootedGermSlabArm.original R Φ L r (e:=a) (N:=d.cutoff) (p:=d.period) w (by rw [tip];exact age) (by rw [tip];exact live)
      (by rw [tip];exact prices.1) (by rw [tip];exact prices.2) (by rw [tip];exact column R warm k)
      (by rw [tip];exact fee)
    exact change_level R tip Z (fun j=>C*β j^t) _ live h
  let g:=regulatorRun R.family d.cutoff d.period k
  have gp : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have pos : 0 ≤ β k := zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have pwr : (g^2*β k)^t ≤ (2:ℝ)^t := pow_le_pow_left₀ (mul_nonneg (sq_nonneg g) pos) (square R d.below) t
  let D:=row R simple J A Q σ d O y
  have small := fine d date O y 1 zero_le_one age (by rw [mul_one];exact fresh)
  change Integrable (fun U=>‖D U‖^(0+1)) ν ∧ (∫ U,‖D U‖^(0+1) ∂ν) ≤ (δ*g^(q+2*t)*1)^(0+1) at small
  simp only [Nat.zero_add,pow_one,mul_one] at small
  have integrableD:= WilsonInvariantActionWithinFine.expense R simple Q J A σ d O y age
  have point (U) : ‖T U‖ ≤ (C*β k^t)*‖D U‖ :=
    (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hOld x U) (norm_nonneg (D U)))
  have product : Integrable T ν := (small.1.const_mul (C*β k^t)).mono'
    ((marked R age d.below Z x).mulC integrableD).1.aestronglyMeasurable (ae_of_all _ point)
  refine ⟨product,?_⟩
  calc
    (∫U,‖T U‖ ∂ν) ≤ ∫U,(C*β k^t)*‖D U‖ ∂ν := by
      apply integral_mono product.norm (small.1.const_mul _)
      exact point
    _ ≤ C*β k^t*(δ*g^(q+2*t)) := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left small.2 (mul_nonneg Cp.le (pow_nonneg pos _))
    _ = δ*g^q*C*(g^2*β k)^t := by rw [pow_add,pow_mul,mul_pow];ring
    _ ≤ δ*g^q*C*(2:ℝ)^t := mul_le_mul_of_nonneg_left pwr (mul_nonneg (mul_nonneg dp.le (pow_nonneg gp _)) Cp.le)
    _ = _ := by dsimp only [δ];field_simp [(ne_of_gt Cp), (pow_ne_zero t (by norm_num : (2:ℝ)≠0))];ring

end YM.Integration.WilsonRootedGermSlabCurvature
