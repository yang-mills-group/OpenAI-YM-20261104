import YM.Integration.ActualWilsonExteriorPrice
import YM.Integration.ActualWilsonCrossedSpectator
import YM.Integration.ActualWilsonRootedNumerator
import YM.Integration.SelectedCofactorExteriorGas

/-! Strong exterior-flag suppression of the actual signed spectator numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonExteriorSpectator
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Extra.Histories Trace.Physical Trace.Physical.GermGraph
open ActualWilsonAxisSpectator ActualWilsonPacketSplit SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem minor (W : Rep G n) {w : ℝ} (hw : w ≤ 1) (H : W.activities.KBound W.p w) (j : ℕ)
    (U : Config G n) : ‖dressed W j U‖ ≤ ActualWilsonExteriorPrice.fee W.p w (flags W.p.threshold U \ scopes W j) := by
  have H' := ActualWilsonExteriorPrice.covered W.activities H hw (scopes W j) U
  rw [ActualWilsonJoinedCofactor.dressed_eq,SelectedCofactorExteriorGas.gas W _ _ (W.activities.forced j).inventory_sup U]
  split
  · rw [Complex.norm_real]
    exact H'.2
  · rw [norm_zero]
    exact budget_nonneg H'.1

theorem paired (X W : Rep G n) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1)
    (HX : X.activities.KBound X.p w) (HW : W.activities.KBound W.p w) (e : ℕ → ℕ)
    (hp : W.p=X.p) (hd : ∀ j, scopes W (e j)=scopes X j) (U : Config G n)
    (y : ℕ → ℂ) {r : ℝ} (H : SumBudget (fun j => X.p.mass (scopes X j) ‖y j‖) r) :
    let P := X.p
    let Fg := flags P.threshold U
    let D j := Fg \ scopes X j
    let f j := y j*((W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U)
    SumBudget (fun j => if (D j).Nonempty then Real.exp (flagRate P*(D j).card)*P.mass (scopes X j) ‖f j‖ else 0)
      ((2*w^2*Real.exp (-flagRate P*Fg.card))*r) := by
  intro P Fg D f
  let B := Real.exp (-flagRate P*Fg.card)
  let a := 2*w^2*B
  have hb : 0 ≤ B := (Real.exp_pos _).le
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  apply budget_mono (budget_scale ha H)
  · intro j
    split
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    · exact le_rfl
  intro j
  by_cases h : (D j).Nonempty
  · rw [if_pos h]
    let b := Real.exp (-flagRate P*(D j).card)
    let t := Real.exp (flagRate P*(D j).card)
    have hF : Fg ≠ ∅ := by
      intro h0
      have he : D j = ∅ := by dsimp only [D]; rw [h0,Finset.empty_sdiff]
      exact h.ne_empty he
    have hx : ‖(X.activities.gas X.p U:ℂ)‖ ≤ w*B := by
      rw [Complex.norm_real]
      apply (ActualWilsonRootedNumerator.vacuum X hw HX U).trans_eq
      change (if Fg=∅ then 1 else w)*B=w*B
      rw [if_neg hF]
    have hW : ‖(W.activities.gas W.p U:ℂ)‖ ≤ w*B := by
      rw [Complex.norm_real]
      apply (ActualWilsonRootedNumerator.vacuum W hw HW U).trans_eq
      rw [hp,if_neg hF]
    have hdX : ‖dressed X j U‖ ≤ w*b := by
      apply (minor X hw HX j U).trans_eq
      change (if D j=∅ then 1 else w)*b=w*b
      rw [if_neg h.ne_empty]
    have hdW : ‖dressed W (e j) U‖ ≤ w*b := by
      apply (minor W hw HW (e j) U).trans_eq
      rw [ActualWilsonExteriorPrice.fee,hp,hd j,if_neg h.ne_empty]
    have hs : ‖(W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U‖ ≤
        2*(w*B)*(w*b) := by
      apply (norm_sub_le _ _).trans
      rw [norm_mul,norm_mul]
      apply (add_le_add (mul_le_mul hW hdX (norm_nonneg _) (mul_nonneg hw0 hb))
        (mul_le_mul hx hdW (norm_nonneg _) (mul_nonneg hw0 hb))).trans_eq
      ring
    have hcancel : t*b=1 := by
      dsimp only [t,b]
      rw [←Real.exp_add,show flagRate P*(D j).card+-flagRate P*(D j).card=0 by ring,Real.exp_zero]
    have hval : t*‖f j‖ ≤ a*‖y j‖ := by
      dsimp only [f]
      rw [norm_mul]
      calc
        _ ≤ t*(‖y j‖*(2*(w*B)*(w*b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) (Real.exp_pos _).le
        _ = (t*b)*(a*‖y j‖) := by dsimp only [a]; ring
        _ = _ := by rw [hcancel,one_mul]
    calc
      _ = Real.exp (P.supportExponent*coverNumber P.B (scopes X j))*(t*‖f j‖) := by unfold BudgetPoint.mass; ring
      _ ≤ Real.exp (P.supportExponent*coverNumber P.B (scopes X j))*(a*‖y j‖) :=
        mul_le_mul_of_nonneg_left hval (Real.exp_pos _).le
      _ = _ := by unfold BudgetPoint.mass; ring
  · rw [if_neg h]
    exact mul_nonneg ha (H.1 j)

theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) {δ : ℝ} {a : ℕ} (H : Bounds S δ a)
    (hFine : I.carrier.rep.eval=(R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (hres : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let X := S.output.carrier.rep
    let W := C.path.rep datum.cutoff datum.period i
    let P := X.p
    let w := C.path.levels.clock.forcedAllowance i
    let Fg := flags P.threshold U
    let out j := Fg \ scopes X j
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let e := ActualWilsonForcedSlots.address X (OriginalForcedAddresses.actual_keeper R hG
      datum.cutoff i datum.period datum.below.le)
    let y j := (D.contents.each j U).part (B.fire v)
    let t := (X.activities.gas X.p U:ℂ)*(Real.exp (-W.exponent U):ℂ)
    let f j := t*(y j*((Real.exp (X.exponent U):ℂ)*dressed X j U-(Real.exp (W.exponent U):ℂ)*dressed W (e j) U))
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)
    let fee := forcedDivisor C i*(F.kernelCosts v*g^a/F.outputRadii v)
    SumBudget (fun j => if (out j).Nonempty then Real.exp (flagRate P*(out j).card)*P.mass (scopes X j) ‖f j‖ else 0)
      ((2*w^2*Real.exp (-flagRate P*Fg.card))*fee) := by
  intro C i X W P w Fg out D e y t f g fee
  have hp : X.p=C.path.levels.budget i := S.output.carrier.point
  have hy : W.p=X.p := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).vac.trans hp.symm
  have hxK : X.activities.KBound X.p w := by rw [hp]; exact S.actual_forced
  have hyK : W.activities.KBound W.p w := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have hw : w ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  obtain ⟨b,hb,hs⟩ := ActualWilsonForcedRow.native_price S H v hres
  have hval (j : ℕ) : ‖y j‖ ≤ b j := by
    exact (congrArg norm (ActualWilsonForcedRow.each_solution D v j U
      (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U))).le.trans ((hb j).2 x U)
  have H' : SumBudget (fun j => X.p.mass (scopes X j) ‖y j‖) fee := by
    rw [hp]
    apply budget_loosen (budget_mono hs (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hval j) (Real.exp_pos _).le))
    apply le_of_eq
    dsimp only [fee,g,C,i]
    ring
  have hd (j : ℕ) : scopes W (e j)=scopes X j := (ActualWilsonForcedSlots.barcode (X := X) _ j).1
  have hall := paired X W (forcedPos C.path.levels i).le hw hxK hyK e hy hd U y H'
  have hf (j : ℕ) : f j=y j*((W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U) :=
    ActualWilsonCrossedSpectator.row X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U) _ _ _
  simp_rw [hf]
  exact hall

end YM.Integration.ActualWilsonExteriorSpectator
