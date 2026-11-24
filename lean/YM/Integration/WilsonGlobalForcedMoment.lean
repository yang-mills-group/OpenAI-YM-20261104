import YM.Integration.SelectedWilsonRootMoment
import YM.Integration.SelectedCofactorFlagRegionPrice
import YM.Integration.SelectedCofactorPriceReadout

/-! Full native weighted price of the complete original forced signed sum
under the true Wilson measure, restricted to an arbitrary thermal hit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGlobalForcedMoment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Cells
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch LocalComparison LocalComparison.Global
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent OPE.Therm OPE.Therm.House
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate SelectedCofactorPacketIntegral
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F} {δ : ℝ} {ord : ℕ}
local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "P₁" => C.path.rep datum.cutoff datum.period (datum.level+1)
local notation "nc" => C.side datum.level datum.period
local notation "nf" => C.side (datum.level+1) datum.period
local notation "w₀" => fun i => F.outputRadii i/F.kernelCosts i
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V*ordinaryRate K I δ)

/-- The complete weighted forced field retains all signed native rows. The
window `X` is used only for the genuine root hit. Other plaquettes can take
arbitrary values, including arbitrary simultaneous exterior flags. -/
theorem selected (hG : G.Simple) (hC : C.Makes) (good : SelectedWilsonRootMoment.Hot C datum.level)
    (S : Chosen K I M) (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval=(P₁).eval) (H : Bounds S δ ord) (x : IndependentTests J.tests) (a : ℝ)
    (paid : ∀ W,Poly.price w₀ (ActualSelectedModelIntegral.defect S (testInclusion J.tests x) W) ≤ a+c₀)
    (X : Finset (Site nc)) (t : Config G nc → ℂ) (ht : Envelope t) (ht1 : ∀W,‖t W‖≤1)
    (hot : ∀W,t W≠0 → ∃ z∈X,z∈flags (cool C.path.levels datum.level) W) :
    ‖∫ W,t W*(Poly.price w₀ (((P₀).eval W)⁻¹ • rooted S x Set.univ (fun _=>True) W):ℂ) ∂scene C.path datum.cutoff datum.period datum.level‖ ≤
      (((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP C.path.levels datum.level)*(a+c₀*r₀) := by
  let y (W : Config G nc) := ((P₀).eval W)⁻¹ • rooted S x Set.univ (fun _ =>True) W
  let f (W : Config G nc) : ℂ := Poly.price w₀ (y W)
  have hw (v : V) : 0 < (w₀) v := div_pos (F.output_radius_positive _) (F.kernel_positive _)
  have hnorm (W : Config G nc) : ‖f W‖ = Poly.price w₀ (y W) := by
    change ‖((Poly.price w₀ (y W):ℝ):ℂ)‖ = _
    rw [Complex.norm_real,Real.norm_of_nonneg (Poly.nonnegative hw _)]
  have hcost (W : Config G nc) : ‖f W‖ ≤ a+c₀*r₀ := by
    obtain ⟨L,hL,key⟩ := SelectedCofactorPriceReadout.norming hw (y W)
    have bill := SelectedCofactorFlagRegionPrice.readout hG hC S hLate hFine H x Set.univ W (fun _ _=>Set.mem_univ _) L hL
    change ‖L (y W)‖ ≤ _ at bill
    rw [key,Complex.norm_real,Real.norm_of_nonneg (Poly.nonnegative hw _)] at bill
    have hd := (hL _).trans (paid W)
    rw [hnorm]
    linarith only [bill,hd]
  have hY : Measurable y := ((P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good).meas.inv.smul
    (rooted_envelope hC S H x Set.univ (fun _=>True)).meas
  have hc : Measurable (fun b : Poly B => Poly.price w₀ b) := by
    unfold Poly.price
    apply Finset.measurable_sum
    intro s _
    exact measurable_const.mul ((Poly.get s).continuous.measurable.norm)
  have hf : Envelope f := ⟨Complex.continuous_ofReal.measurable.comp (hc.comp hY),a+c₀*r₀,hcost⟩
  have neg : Envelope (fun W => -f W) := ⟨hf.meas.neg,a+c₀*r₀,fun W=>by rw [norm_neg]; exact hcost W⟩
  have hn := (norm_nonneg (f (fun _=>1))).trans (hcost (fun _=>1))
  have hzero : Envelope (fun _ : Config G nf => (0:ℂ)) := ⟨measurable_const,0,fun _=>norm_zero.le⟩
  have bound := good datum.cutoff datum.below datum.period X (fun _=>(0:ℂ)) (fun W=> -f W) t hzero neg ht ht1 hot 0 (a+c₀*r₀) le_rfl hn
    (fun _=>norm_zero.le) (fun W=>by rw [norm_neg]; exact hcost W)
  simpa [actualAverage,f,y] using bound

end YM.Integration.WilsonGlobalForcedMoment
