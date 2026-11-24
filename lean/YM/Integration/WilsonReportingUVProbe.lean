import YM.Integration.WilsonReportingUVCenter
import YM.Integration.WilsonReportingSpineCharge

/-! Each genuine angular test on the cost of the returned input reads a
single signed microscopic field. The centered factory subtraction stays
on the same original Wilson measure as all displaced cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVProbe
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source RG12 OPE OPE.Therm
open RG05Readout Native Address Many Records Harvest Extra.Histories
open WilsonMacroscopicRichFlatFibre WilsonReportingUVReturn WilsonReportingUVLikelihood
open WilsonReportingUVCenter Trace.Physical Push.Local
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ) {m d:ℕ}

def residual (t:Letter d) (x:R.family.label (kept t)) (live:m ≤ N) (φ:Body): Goods G (R.family.side N p) :=
  observable R N p t x live φ-specimen t x m N p φ

theorem regular (t:Letter d) (x:R.family.label (kept t)) (live:m ≤ N) (φ:Body) :
    Continuous (residual R N p t x live φ) :=
  (smooth R N p d m (N-m) (by omega) _ (raw_smooth R N p t x) φ).sub
    ((R.family.continuousO ..).const_smul _)

private theorem difference (C:Family G) (h:C.Makes) (X Y:Goods G (C.side N p)) (a:Continuous X) (b:Continuous Y)
    (live:m ≤ N) :
    dyes C m N p live (X-Y) = dyes C m N p live X-dyes C m N p live Y := by
  rw [sub_eq_add_neg,←neg_one_smul ℂ Y,dye_plus h X ((-1:ℂ) • Y) live a (b.const_smul _),dye_pitch,neg_one_smul,sub_eq_add_neg]

theorem measured {b:ℕ} {D:Rail R.family} {B:ℕ→ℕ→ℝ} {V:Sight R.family d p} {U:Emblems R.family d}
    (spine:Spine D B R.makes b p d N V U) (starts:∀e ≤ d,R.family.ref e ≤ N)
    (t:Letter d) (x:R.family.label (kept t)) (aged:R.family.ref (kept t) ≤ m)
    (beginning:b ≤ m) (live:m<N) (φ:Body) (W:Config G (R.family.side m p)) :
    let v:=(R.family.factory (kept t) N p).terminal.symm x
    let y:=Many.point U (chunk t v) N m
    Juniper.Caret.ratio (R.family.path.rep N p m)
        (pulseOut (V m y) φ-WilsonReportingBareCell.centered R.family t v N p m φ) W =
      (∫X,residual R N p t x live.le φ X*likelihood R N p live W X
        ∂scene R.family.path N p N)/(dose (H:=R.family.path) (p:=p) m W N:ℂ) := by
  intro v y
  let X:=observable R N p t x live.le φ
  let Y:=specimen t x m N p φ
  have sx:Continuous X:=smooth R N p d m (N-m) (by omega) _ (raw_smooth R N p t x) φ
  have sy:Continuous Y:=(R.family.continuousO ..).const_smul _
  letI:IsProbabilityMeasure (scene R.family.path N p N):=probability R.makes.wilson le_rfl
  have integrable:Integrable (X-Y) (scene R.family.path N p N):=(sx.sub sy).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have trueX:pulseOut (V m y) φ=dyes R.family m N p live.le X:=
    congrFun (WilsonReportingUVReturn.original R N p spine starts t x beginning live.le) φ
  have trueY:WilsonReportingBareCell.centered R.family t v N p m φ=dyes R.family m N p live.le Y:=
    WilsonReportingUVCenter.centered R.makes (p:=p) t x live.le aged φ
  have both: pulseOut (V m y) φ-WilsonReportingBareCell.centered R.family t v N p m φ=
      dyes R.family m N p live.le (X-Y):=
    (congrArg₂ (fun f g:Goods G (R.family.side m p)=>f-g) trueX trueY).trans
      (difference N p R.family R.makes X Y sx sy live.le).symm
  exact (congrArg (fun f:Goods G (R.family.side m p)=>f W/liftVac R.family.path N p m W) both).trans
    ((exterior_eq R N p live.le (X-Y) W).trans
      (WilsonMacroscopicRichFlatFibre.measured R live le_rfl (X-Y) integrable W))

theorem charge {b:ℕ} {D:Rail R.family} {B:ℕ→ℕ→ℝ} {V:Sight R.family d p} {U:Emblems R.family d}
    (spine:Spine D B R.makes b p d N V U) (starts:∀e ≤ d,R.family.ref e ≤ N)
    (t:Letter d) (x:R.family.label (kept t)) (aged:R.family.ref (kept t) ≤ m)
    (beginning:b ≤ m) (live:m<N) (i:Letter d) (j:Probe G (kept i)) :
    WilsonReportingSpineCharge.charge R.makes t x m N p U V i j=
    Germ.jet R.family.params j (R.family.path.rep N p m).p.threshold 0 (fun W=>
      (∫X,residual R N p t (atK R.family R.makes (kept t) m (N,p) x) live.le (line i) X*
       likelihood R N p live W X ∂scene R.family.path N p N)/
       (dose (H:=R.family.path) (p:=p) m W N:ℂ)) := by
  unfold WilsonReportingSpineCharge.charge
  apply congrArg (Germ.jet R.family.params j (R.family.path.rep N p m).p.threshold 0)
  funext W
  exact measured R N p spine starts t _ aged beginning live (line i) W

end YM.Integration.WilsonReportingUVProbe
