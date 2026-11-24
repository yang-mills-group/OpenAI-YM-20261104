import YM.Integration.WilsonThermometerWeakPairClock
import YM.Integration.WilsonPublicForkInterchange
import YM.Integration.WilsonPublicForkIntegral

/-! The two original source tests may both be signed. The cutoff packet is
integrated through the full chosen horizon before the exterior is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkProfile
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry
open WilsonMacroscopicRichMovingPlane
open scoped Classical Topology
variable {n:ℕ}{G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)

theorem margins (h:ℕ)(fac:Services C f S){K:Set (Points n)}(compact:IsCompact K)(away:K⊆conf n):
    ∀ᶠ r in 𝓝[>] (0:ℝ),∀x∈K,∀k≤h,orbitMargin Q.port k (posed r x) 0:=by
  obtain ⟨M,η,Mn,ηp,placed⟩:=RG17.roomCosts compact away
  let w:Labels S (fun _:Fin 0=>0):=Fin.elim0
  let zero:Labels S (fun _:Fin n=>0):=fun _=>0
  have safe:=profile_scope (ε:=1) F Q fac zero w Mn ηp (show (0:ℝ)<1 by norm_num) zero_lt_one h
  filter_upwards [safe,RG17.positiveLength] with r padded rp x hx k hk
  let y:Fin 0→E4:=Fin.elim0
  have exterior:ClearOf 0 y 1:=⟨fun i=>i.elim0,fun i=>i.elim0⟩
  have room: ((posed r x,(0:E4),y):Loc (Fin n) (Fin 0)) ∈guardZone F Q h:=
    (padded.2 _ (Set.mem_setOf.mpr ⟨placed r rp x hx,exterior⟩)).1
  exact room.1 k hk

theorem joined (ψ:Test n)(φ:Test 2){r t:ℝ}(tp:0<t){d:Fin n→ℕ}{e h:ℕ}(v:∀i,RG17.Free C (d i))(a:RG17.Free C e)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf (n+1))
    (clear:∀x∈tsupport ψ,∀k≤h,orbitMargin Q.port k (posed r x) 0){cost:ℝ}
    (hearing:∀x∈tsupport ψ, ‖reading J φ tp ⟨e,a⟩ r x (fun i=>⟨d i,v i⟩) -
      (stencil J φ tp ⟨e,a⟩).charge F h (Q.packet h (posed r x) (d:=d) (fun i=>J r (d i) (v i)) 0)‖≤cost):
    let X:=stencil J φ tp ⟨e,a⟩
    let u:=fun i=>J r (d i) (v i)
    ‖appeared F (d:=d) u X r ψ-X.charge F h (basket Q h u r ψ)‖ ≤
      (∫x:Points n,‖ψ x‖)*cost:=by
  let X:=stencil J φ tp ⟨e,a⟩
  let u:=fun i=>J r (d i) (v i)
  let Y:=fun x:Points n=>Q.packet h (posed r x) (d:=d) u 0
  let E: S.Field h→L[ℂ]ℂ:=(X.charge F h).toContinuousLinearMap
  have hY:Integrable (fun x:Points n=>ψ x • Y x):=basket_int Q (d:=d) u h ψ clear
  obtain ⟨hZ,eq⟩:=WilsonPublicForkInterchange.original F J ψ φ tp v a safe
  change ‖appeared F (d:=d) u X r ψ-E (∫x:Points n,ψ x • Y x)‖ ≤ _
  rw [eq,←E.integral_comp_comm hY,←integral_sub hZ (E.integrable_comp hY)]
  have hψ:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  refine (norm_integral_le_of_norm_le (hψ.norm.mul_const cost) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
  intro x
  rw [map_smul,smul_eq_mul,←mul_sub,norm_mul]
  by_cases hx:x∈tsupport ψ
  · exact mul_le_mul_of_nonneg_left (hearing x hx) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hx]

end YM.Integration.WilsonPublicForkProfile
