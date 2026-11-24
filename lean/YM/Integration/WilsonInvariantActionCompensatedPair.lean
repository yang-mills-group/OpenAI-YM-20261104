import YM.Integration.WilsonOriginalCompensatedAnchor
import YM.Integration.WilsonInvariantActionPairLimit

/-! The measured action and the prescribed homogeneous spectator can be used
in the same signed two-site readout on the elected physical extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCompensatedPair
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Spin PhysMS
open OPE OPE.Orbits Next.UVStress PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open WilsonInvariantActionPairProbe WilsonInvariantActionPairCovariance WilsonInvariantActionPairLimit
open WilsonPositionHomogeneousFrame
open private free price from YM.Integration.WilsonInvariantActionPairLimit
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
    {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (simple : G.Simple) (w : (standard R.family.labels).Ref 4)

private def moving (r : ℝ) : MaxwellSlots R.family (fun _:Fin 2=>4) :=
  Fin.cons (stepField R.family) (fun _=>
    WilsonPositionPrescribedLift.field F J Z.store 4 r (change F J Z 4 r ((Bel R.family.book).project 4 w)))

include lead paid simple in
theorem original (cent : ∀ᶠr in trail,AlignV F.room.kernel F.sector H (J r 4)) (φ : Test 2) :
    Tendsto (fun r=>tested (J r 4 (stepField R.family))
      (homogeneous F J Z r 4 ((Bel R.family.book).project 4 w)) r φ) trail
    (𝓝 (φ.applyTo (reading R.family w))) := by
  have fields (i : Fin 2) : Tendsto (fun r=>moving F J Z w r i) trail (𝓝 (legs w i)) := by
    fin_cases i
    · exact tendsto_const_nhds
    · exact WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 _
  rw [Metric.tendsto_nhds]
  intro ε he
  let mass:=∫x,‖φ x‖
  have hm : 0 ≤ mass :=integral_nonneg fun _=>norm_nonneg _
  let η:=ε/(2*(mass+1))
  have hp : 0<η:=div_pos he (by positivity)
  have cost : mass*η<ε := by
    dsimp [η]; rw [←mul_div_assoc]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [he,mul_nonneg hm he.le]
  have close:=(WilsonReportingMeasuredAdmission.present F J lead paid).runs F J
    (moving F J Z w) (legs w) fields _ φ.hasCompactSupport φ.tsupport_subset η hp
  filter_upwards [close,cent,self_mem_nhdsWithin] with r hr hc rp
  have centered : centering S 4 (J r 4 (stepField R.family))=J r 4 (stepField R.family) := by
    rw [value_center,hc.cent,sceneV H,zero_smul,sub_zero]
  let tags : Fin 2→S.Tag:=fun i=>⟨4,J r 4 (moving F J Z w r i)⟩
  have charged (x : Points 2) :
      covariance (J r 4 (stepField R.family)) (homogeneous F J Z r 4 ((Bel R.family.book).project 4 w)) x
        = S.classMoment S (fun _=>4) x (fun i=>J r 4 (moving F J Z w r i)) := by
    rw [covariance,centered,placed]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [dist_eq_norm,WilsonInvariantActionPairCovariance.tested]
  simp_rw [charged]
  apply lt_of_le_of_lt _ cost
  apply price
  · exact φ.smearing <| (S.class_smooth S F.room.kernel.smooth tags).continuousOn.comp (by fun_prop)
      (fun _ hz=>Work.A05.smul_conf rp hz)
  · exact φ.smearing ((Bel R.family.book).smooth_read H.smooth _).continuousOn
  intro x hx
  have goal:=free H w (φ.tsupport_subset hx)
  exact goal ▸ hr x hx

end YM.Integration.WilsonInvariantActionCompensatedPair
