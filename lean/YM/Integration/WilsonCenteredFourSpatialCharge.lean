import YM.Integration.WilsonCenteredFourSpatialInterchange

/-! The two original source tests may both be signed. The cutoff packet is
integrated at its actual four-grade horizon before the exterior is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialCharge
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry
open WilsonMacroscopicRichMovingPlane WilsonThermometerWeakPairClock
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)

private lemma margins (fac:Services R.family f S){K:Set (Points 2)}(compact:IsCompact K)(away:K⊆conf 2):
    ∀ᶠ r in trail,∀x∈K,∀k≤4,orbitMargin Q.port k (posed r x) 0:=by
  obtain ⟨M,η,Mn,ηp,placed⟩:=RG17.roomCosts compact away
  let w:Labels S (fun _:Fin 0=>0):=Fin.elim0
  let zero:Labels S (fun _:Fin 2=>4):=fun _=>0
  have safe:=profile_scope (ε:=1) F Q fac zero w Mn ηp (show (0:ℝ)<1 by norm_num) zero_lt_one 4
  filter_upwards [safe,RG17.positiveLength] with r padded rp x hx k hk
  let y:Fin 0→E4:=Fin.elim0
  have exterior:ClearOf 0 y 1:=⟨fun i=>i.elim0,fun i=>i.elim0⟩
  have room: ((posed r x,(0:E4),y):Loc (Fin 2) (Fin 0)) ∈guardZone F Q 4:=
    (padded.2 _ (Set.mem_setOf.mpr ⟨placed r rp x hx,exterior⟩)).1
  exact room.1 k hk

private lemma joined (ψ φ:Test 2){r t:ℝ}(tp:0<t)(v:Fin 2→RG17.Free R.family 4)(a:RG17.Free R.family 4)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf 3)
    (clear:∀x∈tsupport ψ,∀k≤4,orbitMargin Q.port k (posed r x) 0){cost:ℝ}
    (hearing:∀x∈tsupport ψ, ‖reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) -
      (stencil J φ tp ⟨4,a⟩).charge F 4 (Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) (fun i=>J r 4 (v i)) 0)‖≤cost):
    let X:=stencil J φ tp ⟨4,a⟩
    let u:=fun i=>J r 4 (v i)
    ‖appeared F (d:=fun _:Fin 2=>4) u X r ψ-X.charge F 4 (basket Q 4 u r ψ)‖ ≤
      (∫x:Points 2,‖ψ x‖)*cost:=by
  let X:=stencil J φ tp ⟨4,a⟩
  let u:=fun i=>J r 4 (v i)
  let Y:=fun x:Points 2=>Q.packet 4 (posed r x) (d:=fun _:Fin 2=>4) u 0
  let E: S.Field 4→L[ℂ]ℂ:=(X.charge F 4).toContinuousLinearMap
  have hY:Integrable (fun x:Points 2=>ψ x • Y x):=basket_int Q (d:=fun _:Fin 2=>4) u 4 ψ clear
  obtain ⟨hZ,eq⟩:=WilsonCenteredFourSpatialInterchange.original F J ψ φ tp v a safe
  change ‖appeared F (d:=fun _:Fin 2=>4) u X r ψ-E (∫x:Points 2,ψ x • Y x)‖ ≤ _
  rw [eq,←E.integral_comp_comm hY,←integral_sub hZ (E.integrable_comp hY)]
  have hψ:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  refine (norm_integral_le_of_norm_le (hψ.norm.mul_const cost) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
  intro x
  rw [map_smul,smul_eq_mul,←mul_sub,norm_mul]
  by_cases hx:x∈tsupport ψ
  · exact mul_le_mul_of_nonneg_left (hearing x hx) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem original (V:Store G)(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (lead:Leading F J)(salary:WilsonThermometerWeakPairSector.Salary F Q J)(fac:Services R.family f S)
    (v:Fin 2→RG17.Free R.family 4)(K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2)(φ:Test 2):
    ∃(D:ℕ)(C:ℝ),0≤C ∧ ∀(p:ℕ)(ε:ℝ),0<ε→∀ B:ℕ,D+p+1≤B→∀ᶠ r in trail,
      let t:=scale g B r
      let u:=fun i=>J r 4 (v i)
      ∀(tp:0<t)(ψ:Test 2),tsupport ψ⊆K→∀a:RG17.Free R.family 4,
        let X:=stencil J φ tp ⟨4,a⟩
        ‖appeared F (d:=fun _:Fin 2=>4) u X r ψ - X.charge F 4 (basket Q 4 u r ψ)‖ ≤
          (∫x:Points 2,‖ψ x‖)*((∫z:Points 2,‖φ z‖)*(C*‖a‖*(ε*g r^p*(r/t)^4))):=by
  obtain ⟨D,C,c0,point⟩:=WilsonCenteredFourSpatialProfile.original F Q J V simple g hg lead salary v K compact spread φ
  obtain ⟨η,η0,locations⟩:=clearance K compact spread φ
  refine ⟨D,C,c0,?_⟩;intro p ε ep B eligible
  have ratio:Tendsto (fun r=>g r^B) trail (𝓝 (0:ℝ)):=by simpa [zero_pow (by omega:B≠0)] using (hg.conforms simple).pow B
  filter_upwards [point p ε ep B eligible,margins F Q fac compact spread,ratio.eventually (ge_mem_nhds η0),hg.positive,self_mem_nhdsWithin]
    with r paid domain tight gp (rp:0<r)
  dsimp only;intro tp ψ cover a
  have eq:r/scale g B r=g r^B:=by unfold scale;field_simp [rp.ne',gp.ne']
  exact joined F Q J ψ φ tp v a (fun x hx=>locations r _ rp tp (eq.trans_le tight) x (cover hx))
    (fun x hx=>domain x (cover hx)) (fun x hx=>paid tp x (cover hx) a)

end YM.Integration.WilsonCenteredFourSpatialCharge
