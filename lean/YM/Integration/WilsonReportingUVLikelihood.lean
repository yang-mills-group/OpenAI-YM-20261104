import YM.Integration.WilsonReportingUVReturn
import YM.Integration.WilsonMacroscopicRichFlatFibre

/-! One physical microscopic expectation for the entire displaced reporting
row, with its genuine likelihood at the specified coarse gauge field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVLikelihood
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source OPE OPE.Therm Push.GridApprox
open RG05Readout Native Address Many Records Harvest Extra.Histories
open PhysicalNext.Repeat.Legato MergeProof Accent WilsonMacroscopicForwardTransfer
open WilsonMacroscopicRichFlatFibre WilsonReportingUVReturn
open private pushed from YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ) {m:ℕ}

theorem normalized (live:m ≤ N) (X:Goods G (R.family.side N p)) (W:Config G (R.family.side m p)) :
    dyes R.family m N p live X W/liftVac R.family.path N p m W=
      actualTransport R.family (N:=N) X live W := by
  simp only [dyes,Extra.Histories.liftVac,actualTransport,Complex.real_smul,Complex.ofReal_inv,div_eq_inv_mul]

theorem exterior_eq (live:m ≤ N) (X:Goods G (R.family.side N p)) (W:Config G (R.family.side m p)) :
    dyes R.family m N p live X W/liftVac R.family.path N p m W=
      exterior (C:=R.family) (N:=N) live X W := by
  let P:ℂ:=partition G (R.family.side N p) (R.family.path.β N p N)
  have p0:P≠0:=Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  have w0:((R.family.path.rep N p m).eval W:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos R.makes.wilson live W).ne'
  have prices (j:ℕ) (Y:Config G (R.family.side j p)):
      (dose (H:=R.family.path) (p:=p) j Y N:ℂ)=((R.family.path.rep N p j).eval Y:ℂ)/P := by
    simp only [dose,Complex.ofReal_div,P,Family.side]
  have field:weighted (C:=R.family) (N:=N) X=
      fun U=>((R.family.path.rep N p N).eval U:ℂ)*(P⁻¹ • X) U := by
    funext U
    change (dose (H:=R.family.path) (p:=p) N U N:ℂ)*X U=_
    rw [prices]
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_assoc]
  unfold exterior
  rw [field,← pushed (N:=N) (p:=p) (A:=R.family.path) (j:=N) _ live]
  change dyes R.family m N p live X W/((R.family.path.rep N p m).eval W:ℂ)=
    dyes R.family m N p live (P⁻¹ • X) W/(dose (H:=R.family.path) (p:=p) m W N:ℂ)
  rw [dye_pitch,prices]
  change _=P⁻¹*_/_
  field_simp [p0,w0]

def observable {d:ℕ} (t:Letter d) (x:R.family.label (kept t)) (live:m ≤ N) (φ:Body) :
    Goods G (R.family.side N p) := sheets R N p m d (N-m) (by omega) (raw R N p t x) φ

theorem measured {b d:ℕ} {D:Rail R.family} {B:ℕ→ℕ→ℝ}
    {V:Sight R.family d p} {U:Emblems R.family d}
    (spine:Spine D B R.makes b p d N V U) (starts:∀e ≤ d,R.family.ref e ≤ N)
    (t:Letter d) (x:R.family.label (kept t)) (beginning:b ≤ m) (live:m<N)
    (φ:Body) (W:Config G (R.family.side m p)) :
    let y:=Many.point U (chunk t ((R.family.factory (kept t) N p).terminal.symm x)) N m
    Juniper.Caret.ratio (R.family.path.rep N p m) (pulseOut (V m y) φ) W =
      (∫X,observable R N p t x live.le φ X*likelihood R N p live W X
        ∂scene R.family.path N p N)/(dose (H:=R.family.path) (p:=p) m W N:ℂ) := by
  intro y
  let X:=observable R N p t x live.le φ
  letI:IsProbabilityMeasure (scene R.family.path N p N):=probability R.makes.wilson le_rfl
  have smoothX:Continuous X:=smooth R N p d m (N-m) (by omega) _ (raw_smooth R N p t x) φ
  have integrable:Integrable X (scene R.family.path N p N):=
    smoothX.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have original:=congrFun (WilsonReportingUVReturn.original R N p spine starts t x beginning live.le) φ
  change pulseOut (V m y) φ W/liftVac R.family.path N p m W=_
  rw [congrFun original W]
  exact (exterior_eq R N p live.le X W).trans
    (WilsonMacroscopicRichFlatFibre.measured R live le_rfl X integrable W)

end YM.Integration.WilsonReportingUVLikelihood
