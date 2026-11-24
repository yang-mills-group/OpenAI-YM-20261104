import YM.Integration.WilsonThermometerWeakPairMovingOPE
import YM.Integration.WilsonThermometerWeakCornerRows

/-! On the native measured frame the course already issues the nested row
for its reader's own prescription. The collar holds at every positive
polynomial detector exponent on a compact separated shape. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairDetector
open Filter Set Spec Table OPE OPE.Log OPE.Orbits OPE.Arboreal OPE.Nesting EveryPhase
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact.Ascent Frontier6 Frontier6.Tale
open PhysicalNext.Repeat.Legato WilsonThermometerWeakMovingCorner WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open XSpace XSpace.Normalize
open scoped Classical Topology Matrix.Norms.Frobenius
universe u
local notation "child" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position
variable {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{f:Extraction.Order}
    {S:Table R.family.book}(F:Final R.family f S)

theorem gap (simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g){B:ℕ}(bp:0<B)
    {M δ:ℝ}(dp:0<δ):∀ᶠ r in trail,r*M ≤ scale g B r*δ:=by
  have shrinks:Tendsto (fun r=>(g r)^B*M) trail (𝓝 0):=by
    simpa [zero_pow bp.ne'] using ((hg.conforms simple).pow B).mul_const M
  filter_upwards [shrinks.eventually (ge_mem_nhds dp),hg.positive,self_mem_nhdsWithin] with r paid gp rp
  change 0<r at rp
  dsimp only [scale]
  calc
    _ = r/(g r)^B*((g r)^B*M):=by field_simp [gp.ne']
    _ ≤ _:=mul_le_mul_of_nonneg_left paid (div_nonneg rp.le (pow_pos gp _).le)

theorem original {simple:G.Simple}{κ:ℝ}(funded:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(joined:Completed F L)(faculty:Facilities R.family f S)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ→tower S)(V:Store G)(lead:Leading F J)(g:ℝ→ℝ)(hg:Coupling G g)
    (d:↥child→ℕ)(e h:ℕ)(v:∀i,RG17.Free R.family (d i))(w:RG17.Free R.family e)(q:Viewers F)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(A:ℕ)(C:ℝ),0≤C ∧ ∀(B:ℕ),0<B→∀ᶠ r in trail,let t:=scale g B r
      ∀(x y z:E4),‖x‖≤M → ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ →
        let X:=crop (sites r t x y z) child
        ‖formula F Q X 0 (born J r v) (sole (t • z))
          (sole ((far F J e t w).2):Labels S (fun _:Unit=>e)) h q‖≤C/(g r)^A*(r/t)^(h+1):=by
  have H:=WilsonThermometerWeakCornerRows.original F simple funded L joined
  obtain ⟨H₀,Z,U,_,_,_,_,_,_,bliss,_⟩:=H.commonFrame
  have bank:=OPE.tickets_suffice F faculty bliss.lies (agency U bliss.lies) Q.spans
  obtain ⟨A,C,cp,paid⟩:=WilsonThermometerWeakPairMovingOPE.original F H agency Q.spans bank Q book J V lead g hg d e h v w q mn dp
  refine ⟨A,C,cp,fun B bp=>?_⟩
  filter_upwards [paid B,gap simple g hg bp (M:=M) dp] with r income clear
  dsimp only
  exact fun x y z hx hy hz sep xy=>income x y z hx hy hz sep xy clear

end YM.Integration.WilsonThermometerWeakPairDetector
end
