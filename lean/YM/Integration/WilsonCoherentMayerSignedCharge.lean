import YM.Integration.WilsonRetainedSignedStencilPhysical
import YM.Integration.WilsonRetainedStencilIntegrated

/-! The price of the signed finite Wilson stencil in the original centered
Gaussian and gauge orbit, against one arbitrary bounded measurable cofactor.
Each occupied label has its own real linear reading. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSignedCharge
open Filter Function Lattice Wilson RG Pressure Tree Precision ConnectedActivityE6 Finset MeasureTheory
open PhysicalNext.Repeat.Legato RGLocalTaylor RGLocalTaylor.Insert Dict06.Series
open Coat Source Matrix Dict06 AnalyticBridge.LocalGaussianLaws ProbabilityTheory
open WilsonCoherentMayerProjection (restrict Panels)
open WilsonRetainedSignedStencilBooks (books row)
open WilsonRetainedSignedStencilTaylor (Reading material)
open WilsonRetainedSignedStencilPhysical (marked)
open scoped BigOperators Classical ContDiff Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)
variable {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}

theorem smooth (φ:I→Reading) (θ:ℝ) (y:∀i,R.family.label (d i)):
    ContDiff ℝ ω (row R d φ θ y):=by
  let label i:=(R.family.labels.level (d i)).scaled θ⁻¹ (y i)
  have original (A:Panels R d) : row R d φ θ y A=Complex.re (material R d φ label A):=by
    rw [WilsonRetainedSignedStencilTaylor.real_product]
    rfl
  simp_rw [funext original]
  exact Complex.reCLM.contDiff.comp (WilsonRetainedSignedStencilTaylor.smooth R d φ label)

def polynomial (o:I→Site f) (φ:I→Reading) (θ g:ℝ) (y:∀i,R.family.label (d i))
    (p:ℕ) (a:Air f G):ℝ:=∑j∈range (p+1),g^j*PowerSeries.coeff j (books R d F o φ θ y a)

def residual (o:I→Site f) (X:Coat T F) (φ:I→Reading) (θ β g:ℝ) (y:∀i,R.family.label (d i))
    (p:ℕ) (z:momentSpace X):ℝ :=
  marked R d φ θ y o X β z g-polynomial R d (F:=F) o φ θ g y p z.2

theorem measurable {P:Teller G} (fund:P.Funds S T) (o:I→Site f) (X:Coat T F)
    (V:X.V=1) (clear:Assembly.Clear S X.x X.seeds F) (φ:I→Reading) (θ β g:ℝ) (hot:0<β)
    (y:∀i,R.family.label (d i)) (p:ℕ):Measurable (residual R d o X φ θ β g y p):=by
  have grade (j:ℕ) (a:Air f G):PowerSeries.coeff j (books R d F o φ θ y a)=
      Tensor.diagonal (Tensor.coeff (row R d φ θ y) j 0) (restrict R d F o a):=by
    have booked:=(WilsonRetainedSignedStencilBooks.issued R d F o φ θ y a).2
    rw [←booked,ps_at]
    exact radial_eq j ((smooth R d φ θ y).contDiffAt.of_le le_top) _
  have term (j:ℕ):Continuous (fun z:momentSpace X=>PowerSeries.coeff j (books R d F o φ θ y z.2)):=by
    simp_rw [grade]
    exact (Tensor.diag_smooth _ 1).continuous.comp ((restrict R d F o).continuous.comp continuous_snd)
  unfold residual polynomial
  simp_rw [WilsonRetainedSignedStencilPhysical.path R d φ θ y o fund X V clear hot]
  have inputs:Continuous (fun z:momentSpace X=>g•restrict R d F o z.2):=
    ((restrict R d F o).continuous.comp (continuous_snd : Continuous (fun z:momentSpace X=>z.2))).const_smul g
  have raw:Continuous (fun z:momentSpace X=>row R d φ θ y (g•restrict R d F o z.2)):=(smooth R d φ θ y).continuous.comp inputs
  exact raw.measurable.sub (continuous_finsetSum _ (fun j _=>continuous_const.mul (term j))).measurable

theorem original (P:Teller G) (L:Side) (D:Patch) (hd:D.Branches P.bind G) (p:ℕ):
    ∃C:ℝ,0≤C ∧ ∀ᶠ s:ℝ in atTop,∀ (c f:Side) (S:StepData c f) (T:Tube G S)
    (F:Forest S.ratio) (X:Coat T F), X.x=s→S.patch=D→S.patch.L=L→Room P S T s→X.manifest→
    P.Funds S T→X.V=1→Assembly.Clear S X.x X.seeds F→∀o:I→Site f,∀φ:I→Reading,
    (∀i a,|φ i a|≤‖a‖)→∀θ β g:ℝ,0<β→0<g→∀y:∀i,R.family.label (d i),
      ∀W:momentSpace X→ℝ,∀{weight:ℝ},0≤weight→Measurable W→(∀z,|W z|≤weight)→
      let v:=fun z=>W z*residual R d o X φ θ β g y p z
      Integrable v (moment X) ∧ (∫z,|v z| ∂moment X)≤
        weight*(WilsonCoherentReportingPivot.mass R d θ y*(C*g^(p+1))):=by
  obtain ⟨C,hc,stencil⟩:=WilsonRetainedSignedStencilPhysical.purchased R d p
  obtain ⟨K,hk,all⟩:=WilsonRetainedStencilIntegrated.purchased R d P L D hd p
  refine ⟨C*K,mul_nonneg hc hk,?_⟩
  filter_upwards [all] with s bought c f S T F X hx hD hL room hm funds V clear o φ contract θ β g pos hg y W weight hw mw price
  let mass:=WilsonCoherentReportingPivot.mass R d θ y
  have hn : 0 ≤ mass :=by unfold mass WilsonCoherentReportingPivot.mass;exact Finset.sum_nonneg (fun i _=>norm_nonneg _)
  let fee:=mass*(C*g^(p+1))
  have hf:0≤fee:=by unfold fee; positivity
  have point (z:momentSpace X):|residual R d o X φ θ β g y p z|≤fee*‖restrict R d F o z.2‖^(p+1):=by
    apply (stencil φ contract θ y o funds X V clear β pos z g hg).trans_eq
    unfold fee mass
    rw [mul_pow];ring
  obtain ⟨hi,he⟩:=bought c f S T F X hx hD hL room hm o hw hf W (residual R d o X φ θ β g y p)
    mw (measurable R d funds o X V clear φ θ β g pos y p) price point
  refine ⟨hi,he.trans_eq ?_⟩
  unfold fee mass
  ring

end YM.Integration.WilsonCoherentMayerSignedCharge
