import YM.Integration.WilsonRetainedStencilMass
import YM.Integration.WilsonCoherentMayerProjection

/-! The compact Wilson marks on the actual clear conditional sample, with
an all-grade remainder paid on the true finite projected Gaussian stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedStencilPhysical
open Function Lattice RG Pressure Tree Wilson Source ConnectedActivityE6
open RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat.Legato Finset
open Dict06.Series AnalyticBridge.LocalGaussianLaws Precision WilsonRetainedStencilMass
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (R:Run G) {I:Type} [Fintype I] (d:I→ℕ) (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)
open WilsonCoherentMayerProjection

theorem path {P:Teller G} (fund:P.Funds S T) (X:Coat T F) (V:X.V=1)
    (clear:Assembly.Clear S X.x X.seeds F) {β:ℝ} (pos:0<β) (z:momentSpace X) (t:ℝ) :
    WilsonCoherentMayerField.marked R d θ y o X β z t =
      content R d θ y (t • restrict R d F o z.2) :=by
  let Y:=X.wrapY z.1
  have born:Y.input 0=(1:Config G f):=by rw [WilsonCoherentMayerClear.base Y clear,show Y.V=1 from V,replica_one]
  have h:=WilsonCoherentMayerNoise.drawn fund Y V clear pos z.2
  unfold WilsonCoherentMayerField.marked content
  dsimp only
  change (∏i, Push.Local.presented _ (o i) θ (y i) (Y.input ((t*(Coat.gStep β)⁻¹) • Y.liftA β z.2)))=_
  rw [WilsonCoherentMayerField.path,born,h]
  apply prod_congr rfl
  intro i _
  change (R.family.localSection (d i)).evaluate _ (expandAt (o i) (fun e=>G.lieExp (t • WilsonCoherentMayerNoise.row F z.2 e)*(1:Config G f) e))=_
  have placed : expandAt (o i) (fun e=>G.lieExp (t • WilsonCoherentMayerNoise.row F z.2 e)*(1:Config G f) e)=
      Dict06.Wil.positive (expandAt (o i) (WilsonCoherentMayerNoise.row F z.2)) t := by
    funext e
    simp [expandAt,Dict06.Wil.positive]
  rw [placed,Dict06.Wil.echo_exact]
  rfl

/-- Constant before the period, coarse field fibre, placements, positions of
forest trunks, scaled label array, and all Gaussian/Haar samples. -/
theorem purchased (p:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ θ:ℝ, ∀ y:∀i,R.family.label (d i),
    ∀ {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {P:Teller G},
    ∀ o:I→Site f, P.Funds S T → ∀ X:Coat T F, X.V=1→Assembly.Clear S X.x X.seeds F →
    ∀ β:ℝ,0<β→∀ z:momentSpace X, ∀ g:ℝ, 0<g →
      ‖WilsonCoherentMayerField.marked R d θ y o X β z g -
        ∑j∈range (p+1),g^j • PowerSeries.coeff j (books R d F o θ y z.2)‖ ≤
        WilsonCoherentReportingPivot.mass R d θ y*(C*(g*‖restrict R d F o z.2‖)^(p+1)) :=by
  obtain ⟨C,hC,price⟩:=WilsonRetainedStencilMass.purchased R d p
  refine ⟨C,hC,?_⟩
  intro θ y c f S T F P o fund X V clear β pos z g hg
  let A:=restrict R d F o z.2
  have jet (j:ℕ):ordinary j (fun u:ℝ=>content R d θ y (u•A))=PowerSeries.coeff j (books R d F o θ y z.2):=by
    rw [graded]
    exact radial_eq j ((WilsonCoherentMayerProjection.smooth R d θ y).contDiffAt.of_le le_top) A
  rw [path R d θ y o fund X V clear pos,←show
    (∑j∈range (p+1),g^j • ordinary j (fun u:ℝ=>content R d θ y (u•A))) =
    ∑j∈range (p+1),g^j • PowerSeries.coeff j (books R d F o θ y z.2) from
      sum_congr rfl fun i _=>congrArg (fun q:ℂ=>g^i • q) (jet i)]
  exact price θ y A g hg

end YM.Integration.WilsonRetainedStencilPhysical
