import YM.Integration.WilsonIndependentSpoutSchurStory
import YM.Integration.WilsonIndependentConditionalVerse

/-! The same finite Wilson integration with one complete occupied numerator
and its vacuum, in the reporting variable at both ends. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutThermalMark
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior Next.Free
open WilsonIndependentSpoutSchurFrame WilsonIndependentSpoutSchurVacuum
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Side}(S:StepData c f)(T:Forest S.ratio)
    (H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def marked (α:Cost)(Ñ:ChartRatio G)(P W:PChart G f):Ink (Woods G c):=
  Wick (Woods G c) (treeInverse G S T H 0)
    (raiseE (field S T H Y Q α Ñ P)*redo α (loom (camSlice G S T (extractV G S T Q)) (flash W)))

theorem normalized (α:Cost)(unit:constantCoeff α=1){Ñ:ChartRatio G}{P W:PChart G f}
    (p:shellK 2 P)(base:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G)
    (hu:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f)
    (ratio:LocalRatio Ñ)(hf:(treeMatrix G S T H).PosDef)(pure:∀i,Pure (P i))
    (l:ℕ)(span:shellK l W)(pale:∀i,Pure (W i)):
    marked S T H Y Q α Ñ P W=read S T H Y Q α Ñ P*
      redo α (flash (reed S T H Q Ñ P l W)):=by
  let J:Cost:=(α⁻¹)^Fintype.card (Active G T)
  let j:=soil (U:=Woods G c) J
  let d:=read S T H Y Q α Ñ P
  let a:=raiseE (WilsonIndependentSpoutSchurVote.bias α (orbC (precisionC G c Y)))
  have hj:constantCoeff j=1:=by
    have hJ:constantCoeff J=1:=by simp [J,constantCoeff_inv,unit]
    change constantCoeff (soil J)=1
    rw [WilsonIndependentSpoutSchurVote.soil_head,hJ,map_one]
  have paper:j≠0:=by intro h;rw [h,map_zero] at hj;exact zero_ne_one hj
  have vac:=WilsonIndependentSpoutSchurVote.original S T H Y Q α unit p base hz hu hs ratio hf 1
  simp only [map_one,mul_one] at vac
  change d*j=a*redo α (inside S T H Q Ñ P) at vac
  have numerator:=WilsonIndependentSpoutSchurVote.original S T H Y Q α unit p base hz hu hs ratio hf
    (loom (camSlice G S T (extractV G S T Q)) (flash W))
  change marked S T H Y Q α Ñ P W*j=a*redo α (insideMark S T H Q Ñ P W) at numerator
  apply mul_right_cancel₀ paper
  rw [numerator,inside_reed S T H Q l p ratio span hz hs pure pale,map_mul]
  change a*(_*_)=d*_*j
  rw [←mul_assoc,←vac]
  ring

theorem original (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)
    {N m k:ℕ}(finer:m<N)(c:Side)(Z:Era G ℝ)(source:Auth k Z):
    let L:=loose A m;let S:=mStep A c m;let F:=repeatF S
    let H:=freeForms A N (m+1);let Y:=freeForms A N m;let Q:=roam A N m c
    let V:=(story A Ñ N (m+1)).1 (c*L.L)
    let α:=relativeC A Ñ N (m+1) (N-(m+1))
    let α':=relativeC A Ñ N m (N-m)
    marked S F H Y Q α Ñ V (Z.1 (c*L.L))=read S F H Y Q α Ñ V*
      redo α' (flash ((verseI A Ñ m N k Z).1 c)):=by
  intro L S F H Y Q V α α'
  have inlet:Interlace H V:=(old A Ñ simple ratio N (m+1) finer).basis (c*L.L)
  have one:constantCoeff α=1:=angularC simple ratio (by omega)
  have gate:=horizon_step A m N finer c (c*L.L) rfl
  have op:=normalized S F H Y Q α one inlet.lamp inlet.stem (A.blocks m 0).branches gate
    (age_sym A ..) ratio (Convention.tree_pos A m N rfl) inlet.shape k (source.span _) (source.pale _)
  let U:=reed S F H Q Ñ V k (Z.1 (c*L.L))
  have span:shellK k U:=reed_band S F H Q k inlet.lamp ratio (source.span _)
  have lower:(verseI A Ñ m N k Z).1 c=mix (ratioHigh A Ñ N m) U:=rfl
  rw [lower,←redo_stern _ span]
  have changeClock:redo α' (redo (ratioHigh A Ñ N m) (flash U))=redo α (flash U):=by
    unfold α'
    rw [show N-m=1+(N-(m+1)) by omega]
    exact WilsonIndependentSpoutChronologicalClock.original A Ñ simple ratio (by omega) _
  rw [changeClock]
  exact op

end YM.Integration.WilsonIndependentSpoutThermalMark
