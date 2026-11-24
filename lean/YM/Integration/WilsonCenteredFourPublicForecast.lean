import YM.Integration.WilsonCenteredFourOutputSmooth
import YM.Integration.WilsonCenteredFourOutputForecast

/-! One genuine retained-channel price on the moving public prediction. The
fixed logarithm degree is independent of its finite MS coefficient order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourPublicForecast
open Filter Set Table Spec OPE OPE.Orbits OPE.Levy OPE.Log PhysMS Trace Trace.Pilot Trace.Terrace Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater RG12 RG17 SharpGram
open PhysicalNext.Repeat.Legato WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonCenteredFourOutputSensor WilsonMSDictionaryVector GapsContact.Seams
open private bounded from YM.Integration.WilsonCenteredFourOutputForecast
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
local notation "d₄" => (fun _:Fin 2=>4)

theorem original {Y:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{arch:Arch R.family}(simple:G.Simple)
    (bliss:Bliss F l arch Y)(bill:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (V:Store G)(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(c:Q.channels 4):
    ∃k:ℕ,∀(g:ℝ→ℝ),Coupling G g→∀(v:Fin 2→Free R.family 4)(ψ:Test 2)(q:ℕ),∃C:ℝ,0≤C ∧ ∀ᶠr in trail,
      let pred:=prediction R.family d₄ 4 Z M ν v ψ q (g r)
      ‖grade F Q c (homogeneous F J Z r 4 pred)‖≤C*dock r^k*r^4:=by
  obtain ⟨k,H,h0,priced⟩:=WilsonCenteredFourOutputOperator.paid F Q J (simple:=simple) bliss bill V lead c
  obtain ⟨U,u0,bridge⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple 4
  refine ⟨k,?_⟩;intro g hg v ψ q
  let pred:=prediction R.family d₄ 4 Z M ν v ψ q
  have limit:Tendsto (fun r=>pred (g r)) trail (𝓝 (pred 0)):=
    (WilsonCenteredFourOutputForecast.polynomial Z M ν v ψ q).continuousAt.tendsto.comp (hg.conforms simple)
  have good:=limit.eventually ((Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)):Metric.ball (pred 0) 1∈𝓝 (pred 0))
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  refine ⟨H*U*(‖pred 0‖+1),by positivity,?_⟩
  filter_upwards [priced,bridge,good,small,self_mem_nhdsWithin] with r run transfer amp small (rp:0<r)
  let v':=pred (g r)
  have bounded':‖v'‖≤‖pred 0‖+1:=bounded _ _ amp
  have direct:=run (homogeneous F J Z r 4 v') 0
  simp only [map_zero,sub_zero] at direct
  have dock0:0≤dock r:=zero_le_one.trans (dock_valid r ⟨rp,small⟩)
  exact direct.trans ((mul_le_mul_of_nonneg_left ((transfer v').trans (mul_le_mul_of_nonneg_left bounded' u0)) (by positivity)).trans_eq (by ring))
end YM.Integration.WilsonCenteredFourPublicForecast
