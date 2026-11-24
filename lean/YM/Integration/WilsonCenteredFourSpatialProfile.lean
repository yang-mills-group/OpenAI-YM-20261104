import YM.Integration.WilsonCenteredFourSpatialIntegral

/-! The two-site physical detector reads the complete four-grade packet with
the original profile mass and its true moving far-field norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialProfile
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonCenteredFourSpatialNodes WilsonMacroscopicRichSignedAmplitude
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane WilsonThermometerWeakPairClock
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)

theorem original (V:Store G)(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (lead:Leading F J)(salary:WilsonThermometerWeakPairSector.Salary F Q J)
    (v:Fin 2→RG17.Free R.family 4)(K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2)(φ:Test 2):
    ∃(D:ℕ)(C:ℝ),0≤C ∧ ∀(p:ℕ)(ε:ℝ),0<ε→∀ B:ℕ,D+p+1≤B→∀ᶠ r in trail,
      let t:=scale g B r
      let u:=fun i=>J r 4 (v i)
      ∀(tp:0<t)(x:Points 2),x∈K→∀a:RG17.Free R.family 4,
        ‖reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) -
          (stencil J φ tp ⟨4,a⟩).charge F 4 (Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0)‖ ≤
          (∫z:Points 2,‖φ z‖)*(C*‖a‖*(ε*g r^p*(r/t)^4)):=by
  obtain ⟨M,δ,η,m0,δ0,η0,room⟩:=WilsonCenteredFourSpatialSupport.original K compact spread φ
  obtain ⟨D,C,c0,pay⟩:=WilsonCenteredFourSpatialBasis.original F Q J V simple g hg lead salary v m0 δ0
  refine ⟨D,C,c0,?_⟩
  intro p ε ep B eligible
  have ratio:Tendsto (fun r=>g r^B) trail (𝓝 (0:ℝ)):=by simpa [zero_pow (by omega:B≠0)] using (hg.conforms simple).pow B
  filter_upwards [pay p ε ep B eligible,ratio.eventually (ge_mem_nhds η0),hg.positive,self_mem_nhdsWithin]
    with r table tight gp (rp:0<r)
  dsimp only
  intro tp x hx a
  let t:=scale g B r
  let u:=fun i=>J r 4 (v i)
  let Y:=Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0
  have width:r/t≤η:=by
    have eq:r/t=g r^B:=by dsimp [t,scale];field_simp [rp.ne',gp.ne']
    exact eq.trans_le tight
  have gate:=room r t rp tp width x hx
  rw [WilsonCenteredFourSpatialIntegral.original F J φ tp x v a Y (fun z hz=>(gate z hz).2.2.2.2.2.2.2)
    (fun z hz=>⟨(gate z hz).2.2.2.2.2.1,(gate z hz).2.2.2.2.2.2.1⟩)]
  let due:=C*‖a‖*(ε*g r^p*(r/t)^4)
  have nonneg:0≤due:= by dsimp [due];positivity
  have ph:Integrable φ:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  refine (norm_integral_le_of_norm_le (ph.norm.mul_const due) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
  intro z
  by_cases hz:z∈tsupport φ
  · obtain ⟨x0,x1,hi,lo,nc,c1,c2,_⟩:=gate z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (table x (relative z 0) x0 x1 hi lo nc c1 c2 a) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

end YM.Integration.WilsonCenteredFourSpatialProfile
