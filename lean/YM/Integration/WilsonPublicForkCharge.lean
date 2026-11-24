import YM.Integration.WilsonPublicForkMixed
import YM.Integration.WilsonPublicForkProfile

/-! A selected finite family of literal physical inputs and the full measured
output, in the original order, on the matrix ticket of the original extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkCharge
open Function Finset Filter Set Table Spec Climb OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace WilsonPublicForkLabels WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open MeasureTheory WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
  {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem original {simple:G.Simple}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(done':Completed F L)(fac:Facilities R.family f S)
    {𝓛:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arc Y)(ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ → tower S)(V:Store G)(lead:Leading F J)(g:ℝ → ℝ)(hg:Coupling G g)
    {n:ℕ}(d:Fin n → ℕ)(e h:ℕ)(K:Set (Points n))(compact:IsCompact K)(spread:K⊆conf n)(φ:Test 2):
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀B:ℕ,0<B → ∀ᶠ r in trail,let t:=scale g B r
      ∀(tp:0<t)(v:∀i,RG17.Free R.family (d i))(a:RG17.Free R.family e)(ψ:Test n),tsupport ψ⊆K →
      let X:=stencil J φ tp ⟨e,a⟩
      let u:=fun i=>J r (d i) (v i)
      ‖appeared F (d:=d) u X r ψ-X.charge F h (basket Q h u r ψ)‖≤
        (∫x:Points n,‖ψ x‖)*((∫z:Points 2,‖φ z‖)*(C*(∏i,‖v i‖)*‖a‖*((r/t)^(h+1)/(g r)^E))):=by
  obtain ⟨M,δ,η,mn,dp,ηp,room⟩:=WilsonPublicForkSupport.original K compact spread φ
  obtain ⟨E,C,cp,physical⟩:=WilsonPublicForkMixed.original F fund L done' fac bliss ticket Q book J V lead g hg d e h mn dp
  refine ⟨E,C,cp,fun B bp=>?_⟩
  have ratio:Tendsto (fun r=>g r^B) trail (𝓝 (0:ℝ)):=by simpa [zero_pow bp.ne'] using (hg.conforms simple).pow B
  have width:0<δ/(M+1):=div_pos dp (by linarith)
  filter_upwards [physical B,ratio.eventually (ge_mem_nhds ηp),ratio.eventually (ge_mem_nhds width),hg.positive,
     WilsonPublicForkProfile.margins F Q h fac.toServices compact spread,self_mem_nhdsWithin]
    with r table clear close gp margin (rp:0<r)
  let t:=scale g B r
  dsimp only
  intro tp v a ψ inside
  have eq:r/t=g r^B:=by dsimp [t,scale];field_simp [rp.ne',gp.ne']
  have wide:r*M≤t*δ:=by
    have paid: r/t*(M+1)≤δ:=(le_div_iff₀ (by linarith:0<M+1)).mp (eq.trans_le close)
    rw [mul_comm t δ]
    apply (div_le_iff₀ tp).mp
    calc r*M/t=(r/t)*M:=by ring
         _≤δ:=by have:=div_nonneg rp.le tp.le;nlinarith
  apply WilsonPublicForkProfile.joined F Q J ψ φ tp v a
  · exact fun x hx z hz=>(room r t rp tp (eq.trans_le clear) x (inside hx) z hz).2.2.2.2.2.2
  · exact fun x hx=>margin x (inside hx)
  · intro x hx
    let gate:=room r t rp tp (eq.trans_le clear) x (inside hx)
    have prob:=WilsonPublicForkIntegral.original F J φ tp x v a (Q.packet h (posed r x) (d:=d) (fun i=>J r (d i) (v i)) 0)
      (fun z hz=>(gate z hz).2.2.2.2.2.2) (fun z hz=>⟨(gate z hz).2.2.2.2.1,(gate z hz).2.2.2.2.2.1⟩)
    rw [prob]
    let fee:=C*(∏i,‖v i‖)*‖a‖*((r/t)^(h+1)/(g r)^E)
    have p0:0≤fee:=by dsimp only [fee];positivity
    have ph:Integrable φ:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    refine (norm_integral_le_of_norm_le (ph.norm.mul_const fee) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
    intro z
    by_cases hz:z∈tsupport φ
    · obtain ⟨near,far,twice,ap,cl,ext,_⟩:=gate z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (table x (relative z 0) near far twice ap wide cl ext v a) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
end YM.Integration.WilsonPublicForkCharge
