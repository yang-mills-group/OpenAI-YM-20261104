import YM.Integration.WilsonCenteredFourSpatialCharge
import YM.Integration.WilsonCenteredFourSpatialMixed

/-! The finite experiment may choose each of its three running colors after r.
Both signed profile integrations are on their actual separated supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialMixedCharge
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonCenteredFourSpatialNodes WilsonMacroscopicRichSignedAmplitude
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane WilsonThermometerWeakPairClock
open private joined margins from YM.Integration.WilsonCenteredFourSpatialCharge
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)

theorem original (V:Store G)(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (lead:Leading F J)(salary:WilsonThermometerWeakPairSector.Salary F Q J)
    (fac:Services R.family f S)(K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2)(φ:Test 2):
    ∃(D:ℕ)(C:ℝ),0≤C ∧ ∀(p:ℕ)(ε:ℝ),0<ε→∀ B:ℕ,D+p+1≤B→∀ᶠ r in trail,
      let t:=scale g B r
      ∀(tp:0<t)(v:Fin 2→RG17.Free R.family 4)(a:RG17.Free R.family 4),
      let u:=fun i=>J r 4 (v i)
      let X:=stencil J φ tp ⟨4,a⟩
      let cost:=(∫z:Points 2,‖φ z‖)*(C*(∏i,‖v i‖)*(‖a‖*(ε*g r^p*(r/t)^4)))
      (∀x∈K, ‖reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) -
           X.charge F 4 (Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0)‖ ≤cost) ∧
      ∀(ψ:Test 2),tsupport ψ⊆K→
        ‖appeared F (d:=fun _:Fin 2=>4) u X r ψ-X.charge F 4 (basket Q 4 u r ψ)‖≤(∫x:Points 2,‖ψ x‖)*cost:=by
  obtain ⟨M,δ,η,m0,δ0,η0,room⟩:=WilsonCenteredFourSpatialSupport.original K compact spread φ
  obtain ⟨D,C,c0,pay⟩:=WilsonCenteredFourSpatialMixed.original F Q J V simple g hg lead salary m0 δ0
  refine ⟨D,C,c0,?_⟩
  intro p ε ep B eligible
  have ratio:Tendsto (fun r=>g r^B) trail (𝓝 (0:ℝ)):=by simpa [zero_pow (by omega:B≠0)] using (hg.conforms simple).pow B
  filter_upwards [pay p ε ep B eligible,ratio.eventually (ge_mem_nhds η0),margins F Q fac compact spread,hg.positive,self_mem_nhdsWithin]
    with r table tight domain gp (rp:0<r)
  dsimp only
  intro tp v a
  let t:=scale g B r
  let u:=fun i=>J r 4 (v i)
  have width:r/t≤η:=by
    have eq:r/t=g r^B:=by dsimp [t,scale];field_simp [rp.ne',gp.ne']
    exact eq.trans_le tight
  have hearing:∀x∈K, ‖reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩)-
      (stencil J φ tp ⟨4,a⟩).charge F 4 (Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0)‖≤
      (∫z:Points 2,‖φ z‖)*(C*(∏i,‖v i‖)*(‖a‖*(ε*g r^p*(r/t)^4))):=by
    intro x hx
    let Y:=Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0
    have gate:=room r t rp tp width x hx
    rw [WilsonCenteredFourSpatialIntegral.original F J φ tp x v a Y (fun z hz=>(gate z hz).2.2.2.2.2.2.2)
      (fun z hz=>⟨(gate z hz).2.2.2.2.2.1,(gate z hz).2.2.2.2.2.2.1⟩)]
    let due:=C*(∏i,‖v i‖)*(‖a‖*(ε*g r^p*(r/t)^4))
    have nonneg:0≤due:= by dsimp [due];positivity
    have ph:Integrable φ:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    refine (norm_integral_le_of_norm_le (ph.norm.mul_const due) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
    intro z
    by_cases hz:z∈tsupport φ
    · obtain ⟨x0,x1,hi,lo,nc,c1,c2,_⟩:=gate z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (table x (relative z 0) x0 x1 hi lo nc c1 c2 v a) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  refine ⟨hearing,fun ψ included=>joined F Q J ψ φ tp v a ?_ ?_ ?_⟩
  · exact fun x hx z hz=>(room r t rp tp width x (included hx) z hz).2.2.2.2.2.2.2
  · exact fun x hx=>domain x (included hx)
  · exact fun x hx=>hearing x (included hx)

end YM.Integration.WilsonCenteredFourSpatialMixedCharge
