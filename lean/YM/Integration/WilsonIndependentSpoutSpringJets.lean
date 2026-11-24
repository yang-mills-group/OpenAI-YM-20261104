import YM.Integration.WilsonIndependentSpoutSpringAction

/-! Exact unintegrated thermal spring on the two real held-field directions. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutSpringJets
open Set Filter Lattice RG WilsonCoeffUV RegulatorIR RegulatorIR.Geometry RegulatorIR.Prim
open RegulatorIR.Geometry.Field
open RegulatorIR.Binding RegulatorIR.Laplace PertExtension PertExtension.Orb Tree Tree.Forest
open WilsonIndependentSpoutSpringAction
open scoped Classical Topology ContDiff
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(N:Scale)

theorem original (hc:Even c.val)(hf:Even f.val)(Z:S.patch.Branches S.kernel G)
    (y:Meadow G (Wind F))(b:Horizon G c):
    inscription (priceMap (nextO S F N)) (y,1,b)=
      tale (fun t:ℝ=>N.beta t*(jointPen G S (both (t • injectX F y) (t • b))/2)) := by
  let x:Meadow G (Wind F) × ℝ × Horizon G c:=(y,1,b)
  have smooth:ContDiffAt ℝ ∞ (priceMap (nextO S F N) :
      Meadow G (Wind F) × ℝ × Horizon G c → ℝ) 0 := (nextF N S Z).smooth
  rw [←lore smooth]
  symm
  apply tale_eq
  · have radial:ContDiffAt ℝ ∞ (fun t:ℝ=>t • x) 0:=contDiffAt_id.smul contDiffAt_const
    have rest:ContDiffAt ℝ ∞ (priceMap (nextO S F N)) ((0:ℝ) • x):=by rwa [zero_smul]
    exact rest.comp 0 radial
  · have t:Tendsto (fun r:ℝ=>r • injectX F y) (𝓝 0) (𝓝 0):=by
      have h:Continuous (fun r:ℝ=>r • injectX F y):=continuous_id.smul continuous_const
      simpa only [zero_smul] using h.tendsto 0
    filter_upwards [t.eventually (native S hc hf Z)] with r hr
    change N.beta r*(jointPen G S (both (r • injectX F y) (r • b))/2)=
      N.beta (r*1)*bond S (Field.cloth F (Chart.expLinks G _ (r • y))) (climb (r • b))
    rw [mul_one,chart_commute,map_smul,hr]
    ring

end YM.Integration.WilsonIndependentSpoutSpringJets
