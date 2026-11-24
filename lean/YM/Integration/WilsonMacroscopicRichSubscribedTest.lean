import YM.Integration.WilsonMacroscopicRichAllInputs
import YM.Integration.WilsonMacroscopicRichSignedAmplitude

/-! Signed detector for jointly varying incoming fields and an independently varying detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSubscribedTest
open Function Filter MeasureTheory Set Finset YM YM.Table YM.Climb YM.PhysMS YM.Trace.Pilot YM.Next.UVStress YM.RG17
open WilsonMacroscopicRichReflectedRoster WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane WilsonMacroscopicRichSignedAmplitude
open private field from YM.Integration.WilsonMacroscopicRichSignedAmplitude
open private agree from YM.Integration.WilsonMacroscopicRichAllInputs
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{n:ℕ}

/-- The two independent absolute dates need not have a specified functional relation. -/
theorem original (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J)(d:Caps (n+1))(φ:Test 2)(K:Set (Points n))
    (compact:IsCompact K)(safe:K⊆conf n):∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,∀tp:0<τ,r/τ≤η →∀x∈K,∀u:∀i,(Bel C.book).Field (d i),
    let tags:Fin (n+1)→(Bel C.book).Tag:=fun i=>⟨d i,u i⟩
    ‖reading J φ tp (tags (Fin.natAdd n 0)) r x (fun i=>tags (Fin.castAdd 1 i))‖≤
      (∫z:Points 2,‖φ z‖)*B*∏i,‖u i‖:=by
  obtain ⟨c,cp,space⟩:=clearance K compact safe φ
  obtain ⟨far,nz⟩:=WilsonMacroscopicRichTestGeometry.support φ
  obtain ⟨a,ap,B,bp,U,hU,bill⟩:=WilsonMacroscopicRichAllInputs.original F J H d K _ compact far safe nz
  refine ⟨min a c,lt_min ap cp,B,bp,U∩Ioi 0,inter_mem hU self_mem_nhdsWithin,?_⟩
  intro r hr τ hτ tp ratio x hx u
  let tags(i:Fin (n+1)):(Bel C.book).Tag:=⟨d i,u i⟩
  let w:=tags (Fin.natAdd n 0);let v(i:Fin n):=tags (Fin.castAdd 1 i)
  let zfield:=integrand J φ tp w r x v
  let D:=B*∏i,‖u i‖
  have positive:0≤D:=mul_nonneg bp (prod_nonneg fun i _=>norm_nonneg _)
  have T:Integrable (fun z:Points 2=>φ z):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have budget(z:Points 2):‖φ z*zfield z‖ ≤‖φ z‖*D:=by
    by_cases hz:z∈tsupport φ
    · rw [norm_mul];apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have clear:=space r τ hr.2 tp (ratio.trans (min_le_right _ _)) x hx z hz
      rw [show zfield z= _ from field F J φ tp w r x v clear]
      rw [←agree J d u r τ x (relative z)]
      exact bill r hr.1 τ hτ.1 (ratio.trans (min_le_left _ _)) x hx _ ⟨z,hz,rfl⟩ u
    · simp [image_eq_zero_of_notMem_tsupport hz]
  change ‖(Next.UVStress.dilate tp φ).applyTo _‖ ≤ _
  rw [Next.UVStress.zoom_integral]
  change ‖∫ z,φ z*zfield z‖ ≤ _
  calc _ ≤ ∫ z:Points 2,‖φ z‖*D := norm_integral_le_of_norm_le (T.norm.mul_const D) (ae_of_all _ budget)
       _=(∫z:Points 2,‖φ z‖)*B*∏i,‖u i‖:= by rw [integral_mul_const];dsimp [D];ring
end YM.Integration.WilsonMacroscopicRichSubscribedTest
