import YM.Integration.WilsonPublicForkIndependentFields

/-! The prescribed kernels at the original reflected detector. Near slots
are positioned in their own units; the outer slot uses its own displacement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkCanonicalKernels
open Filter Function Set Finset MeasureTheory PowerSeries FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.O.Project FVA2.Scale FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake PhysMS Trace.Pilot
open WilsonMSDictionaryFarRead WilsonMSDictionaryVector WilsonPublicForkIndependentWindow
open WilsonPublicForkIndependentPlacement WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonPublicForkIndependentHearing
open scoped Classical Topology BigOperators
variable {G:Gauge}{n h:ℕ}
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

def many (q:ℕ)(g s:ℝ)(u:Scan G n)(v:Scan G 1)(p:Points n×Points 2):ℂ:=
  fee s (-(totalG v:ℝ))*cutoff q g (joint Z u v p.1 (relative p.2) s)

def pair (q:ℕ)(g s:ℝ)(v:Scan G 1)(b:Dframe.Toon G h)(z:Points 2):ℂ:=
  fee s (-(totalG v:ℝ))*cutoff q g (leg Z v b (relative z) s)

include ν ms in
theorem regular (q:ℕ)(g s:ℝ)(ψ:Test n)(φ:Test 2)
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1)):
    (∀u v,ContinuousOn (many Z q g s u v) (space ψ φ)) ∧
    (∀v (b:Dframe.Toon G h),ContinuousOn (pair Z q g s v b) (tsupport φ)):=by
  let source:=(ms.separatedOPE ν).wilson
  have shifted:Continuous (fun z:Points 2=>squeeze (-s) (relative z)):=
    (continuous_const_smul _).comp continuous_relative
  constructor
  · intro u v;apply continuousOn_const.mul;apply continuous_cut;intro k _
    exact (source.awake _ _ k).comp (continual continuous_fst (shifted.comp continuous_snd)).continuousOn fit
  · intro v b;apply continuousOn_const.mul;apply continuous_cut;intro k _
    apply (source.awake _ _ k).comp (continual continuous_const shifted).continuousOn
    intro z hz;exact lives (-s) (WilsonPublicForkIndependentPlacement.outside φ ⟨z,hz,rfl⟩)

end YM.Integration.WilsonMovingForkCanonicalKernels
