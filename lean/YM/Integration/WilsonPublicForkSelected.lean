import YM.Integration.WilsonPublicForkLabels
import YM.Integration.WilsonPublicForkMoving
import YM.Integration.WilsonThermometerWeakPairDetector

/-! A selected finite family of literal physical inputs and the full measured
output, in the original order, on the matrix ticket of the original extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkSelected
open Function Finset Filter Set Table Spec Climb OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace WilsonPublicForkLabels WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open scoped Classical Topology BigOperators
universe u
variable {I:Type} [Fintype I] {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
  {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem original {simple:G.Simple}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(done':Completed F L)(fac:Facilities R.family f S)
    {𝓛:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arc Y)(ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ → tower S)(V:Store G)(lead:Leading F J)(g:ℝ → ℝ)(hg:Coupling G g)
    (d:I → ℕ)(e h:ℕ)(v:∀i,Free R.family (d i))(w:Free R.family e)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(A:ℕ)(C:ℝ),0≤C ∧ ∀B:ℕ,∀ᶠ r in trail,let t:=scale g B r
      ∀(x:I → E4)(z:E4),(∀i,‖x i‖≤M) → ‖z‖≤M → 2*δ≤‖z‖ → (∀i j,i≠j → δ≤‖x i-x j‖) → r*M≤t*δ → 
      Injective (beside (fun i=>r • x i) (sole (t • z))) → Injective (beside (sole (0:E4)) (sole (t • z))) → 
      let u:=fun i=>J r (d i) (v i)
      ‖defect e h (fun i=>r • x i) u (Q.packet h (fun i=>r • x i) u 0) (t • z) (J t e w)‖≤C/g r^A*(r/t)^(h+1):=by
  let H:=WilsonThermometerWeakCornerRows.original F simple fund L done'
  have bank:=OPE.tickets_suffice F fac bliss.lies ticket Q.spans
  obtain ⟨A,C,cp,sale⟩:=WilsonPublicForkMoving.original F H bliss ticket Q.spans bank Q book J V lead g hg
    (d ∘ index (I:=I)) e h (fun j=>v (index j)) (reflect e w) none mn dp
  refine ⟨A,C,cp,fun B=>?_⟩
  filter_upwards [sale B,(small simple g hg B).eventually (lead.equivariant e)] with r actual eq
  dsimp only;intro x z hx hz fz sep gap inside outside'
  have measured:=actual x z hx hz fz sep gap
  let t:=scale g B r
  let u:=fun i=>J r (d i) (v i)
  have parity:(WilsonThermometerWeakMovingCorner.far F J e t (reflect e w)).2=J t e w:=by
    exact (Frame.flip_coupled F e J t eq (reflect e w)).symm.trans
      (congrArg (J t e) ((Bel R.family.book).reflect_twice _ e timeAxis w))
  rw [slots,parity] at measured
  exact (congrArg norm (signed F Q (fun i=>r • x i) u (t • z) (J t e w) inside outside')).symm.trans_le measured
end YM.Integration.WilsonPublicForkSelected
