import YM.Integration.ActualWilsonCrossedExposure
import YM.Integration.ActualWilsonSpectatorDifference

/-! The complete signed spectator through the true physical model defect and the original Wilson minor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPhysicalDefect
open MeasureTheory Function Filter Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonForcedSlots ActualWilsonSpectatorDifference
open SelectedCofactorCancellation ActualSelectedModelIntegral ActualSelectedCoveredCofactor SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem components (X W : Rep G n) {w : ℝ} (hw : w≤1)
    (hX : X.activities.KBound X.p w) (hW : W.activities.KBound W.p w)
    (e : ℕ → ℕ) (U : Config G n) (y : ℕ → ℂ) {fee : ℝ} (H : SumBudget (fun j => ‖y j‖) fee) :
    let a j := y j*dressed X j U
    let b j := y j*dressed W (e j) U
    let ex := (Real.exp (X.exponent U):ℂ)
    let ew := (Real.exp (W.exponent U):ℂ)
    (∑' j,y j*(ex*dressed X j U-ew*dressed W (e j) U))=ex*(∑' j,a j)-ew*(∑' j,b j) ∧
      ‖∑' j,b j‖≤fee := by
  intro a b ex ew
  have hA : SumBudget (fun j => ‖a j‖) fee := budget_mono H (fun j => norm_nonneg _) (fun j => by
    rw [show a j=y j*dressed X j U from rfl,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ActualWilsonSpectatorBudget.dressed_le_one hX hw j U))
  have hB : SumBudget (fun j => ‖b j‖) fee := budget_mono H (fun j => norm_nonneg _) (fun j => by
    rw [show b j=y j*dressed W (e j) U from rfl,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ActualWilsonSpectatorBudget.dressed_le_one hW hw (e j) U))
  refine ⟨?_,(norm_tsum_le_tsum_norm hB.2.1).trans hB.2.2⟩
  calc
    _ = ∑' j,(ex*a j-ew*b j) := tsum_congr (fun j => by dsimp only [a,b];ring)
    _ = _ := by rw [(hA.2.1.of_norm.mul_left ex).tsum_sub (hB.2.1.of_norm.mul_left ew),tsum_mul_left,tsum_mul_left]

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    {δ : ℝ} {a : ℕ} (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V)≤datum.level)
    (hFine : I.carrier.rep.eval=(R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let X := S.output.carrier.rep
    let W := C.path.rep datum.cutoff datum.period i
    let w := C.path.levels.clock.forcedAllowance i
    let fee := F.kernelCosts v*(forcedDivisor C i*Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)^a/F.outputRadii v)
    let test := testInclusion J.tests x
    let D := S.output.residual.leaf test
    let e := address X (OriginalForcedAddresses.actual_keeper R hG datum.cutoff i datum.period datum.below.le)
    let b := ∑' j,((D.contents.each j U).part (B.fire v))*dressed W (e j) U
    let d := (defect S test U).part (B.fire v)-(D.log U).part (B.fire v)
    let f := (Real.exp (-W.exponent U):ℂ)*spectator R hG S x v U
    f=(W.activities.gas W.p U:ℂ)*d-b ∧ ‖b‖≤fee ∧ ‖f‖≤w*‖d‖+fee := by
  intro C i X W w fee test D e b d f
  let y j := (D.contents.each j U).part (B.fire v)
  let α := (Real.exp (X.exponent U):ℂ)
  let β := (Real.exp (W.exponent U):ℂ)
  let z := (Real.exp (-W.exponent U):ℂ)
  let sx := ∑' j,y j*dressed X j U
  have hW := R.makes.wilson.represents datum.cutoff datum.period i datum.below.le
  have hx : X.activities.KBound X.p w := by rw [show X.p=C.path.levels.budget i from S.output.carrier.point];exact S.actual_forced
  obtain ⟨v0,hv0,hpaid⟩ := ActualWilsonForcedRow.retained S H v
  have H0 : SumBudget (fun j => ‖y j‖) fee := budget_mono hpaid (fun j => norm_nonneg _) (fun j =>
    ((congrArg norm (ActualWilsonForcedRow.each_solution D v j U
      (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U))).le.trans ((hv0 j).2 x U)).trans
      ((A.outputNorm i).loMass _ _ (hv0 j).1))
  have hw1 : w≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  obtain ⟨hs,hb⟩ := components X W hw1 hx hW.good.labels.boundK e U y H0
  have hspec : spectator R hG S x v U=α*sx-β*b := hs
  have hrows : singletonRows D U v=sx := by
    unfold singletonRows
    apply tsum_congr
    intro j
    simp only [y,dressed,coat_pinned]
    rfl
  have hnu := congrArg (fun pp : Poly B => pp.part (B.fire v))
    (ActualSelectedCofactorFunding.weighted_identity hG R.makes S hLate hFine H x U)
  have hn := numerator_singleton hG R.makes S hLate H x U v
  have hh : (W.eval U:ℂ)*((defect S test U).part (B.fire v))=
      (W.eval U:ℂ)*(D.log U).part (B.fire v)+α*singletonRows D U v := hnu.trans hn
  rw [hrows] at hh
  have hc : α*sx=(W.eval U:ℂ)*d := by dsimp only [d];linear_combination -hh
  have hinv : z*β=1 := by
    dsimp only [z,β]
    rw [←Complex.ofReal_mul,←Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  have he : z*(W.eval U:ℂ)=(W.activities.gas W.p U:ℂ) := by
    change z*(↑(Real.exp (W.exponent U)*W.activities.gas W.p U):ℂ)=_
    rw [Complex.ofReal_mul,←mul_assoc,hinv,one_mul]
  have hid : f=(W.activities.gas W.p U:ℂ)*d-b := by
    change z*spectator R hG S x v U=_
    rw [hspec,hc,mul_sub,←mul_assoc,←mul_assoc,he,hinv,one_mul]
  refine ⟨hid,hb,?_⟩
  by_cases hF : flags W.p.threshold U=∅
  · have hpW : W.p=C.path.levels.budget i := hW.vac
    have h0 : flags (C.path.levels.budget i).threshold U=∅ := by simpa only [hpW] using hF
    have hz := ActualWilsonSpectatorGerm.clean R hG S U h0 x v
    change ‖z*spectator R hG S x v U‖≤_
    rw [hz,mul_zero,norm_zero]
    exact add_nonneg (mul_nonneg (forcedPos C.path.levels i).le (norm_nonneg _)) (budget_nonneg H0)
  have hg : ‖(W.activities.gas W.p U:ℂ)‖≤w := by
    rw [Complex.norm_real]
    apply (ActualWilsonRootedNumerator.vacuum W hw1 hW.good.labels.boundK U).trans
    rw [if_neg hF]
    apply mul_le_of_le_one_right (forcedPos C.path.levels i).le
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (flagRate_pos _).le) (Nat.cast_nonneg _))
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))) hb)

end YM.Integration.ActualWilsonPhysicalDefect
