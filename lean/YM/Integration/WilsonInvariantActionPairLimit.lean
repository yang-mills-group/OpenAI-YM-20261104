import YM.Integration.WilsonInvariantActionPairProbe
import YM.Integration.WilsonInvariantActionPairCovariance

/-! The actual measured action against the elected Maxwell spectator has the
tested free response as its limit, including the original central subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairLimit
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Spin PhysMS
open OPE OPE.Orbits Next.UVStress WilsonInvariantActionPairProbe WilsonInvariantActionPairCovariance
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (J : ℝ→tower S) (H : (Bel C.book).Hierarchy)
  (w : (standard C.labels).Ref 4)

def legs : MaxwellSlots C (fun _:Fin 2=>4) :=
  Fin.cons (stepField C) (fun _=>(Bel C.book).project 4 w)

include H in
private theorem free {x : Points 2} (hx : x∈conf 2) :
    WickGoal (legs w) x=reading C w x := by
  let B:=Bel C.book
  let a : Fin 2→(standard C.labels).Ref 4 := Fin.cons (B.representative 4 (stepField C)) (fun _=>w)
  have loc : (fun i=>B.project 4 (a i))=legs w := by
    funext i
    fin_cases i <;> simp [a,legs,B.rep]
  change B.classMoment B (fun _=>4) x (legs w)=_
  rw [←loc,B.class_agrees B H.laws.toSymmetric (fun _=>le_rfl) _ hx a]
  have letters : (fun i=>(⟨4,a i⟩:(standard C.labels).Token))=
      Fin.cons ⟨4,B.representative 4 (stepField C)⟩ (fun _=>⟨4,w⟩) := by
    funext i
    fin_cases i <;> rfl
  change B.read x (fun i=>⟨4,a i⟩)=_
  rw [letters]
  rfl

private theorem price (φ : Test 2) {v t : Points 2→ℂ} (hv : Integrable (fun x=>φ x*v x))
    (ht : Integrable (fun x=>φ x*t x)) {a : ℝ}
    (bound : ∀x∈tsupport (φ:Points 2→ℂ), ‖v x-t x‖≤a) :
    ‖φ.applyTo v-φ.applyTo t‖≤(∫x,‖φ x‖)*a := by
  unfold Test.applyTo
  rw [←integral_sub hv ht]
  have bank : Integrable (fun x : Points 2=>φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  apply (norm_integral_le_of_norm_le (bank.norm.mul_const a) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
  intro x
  rw [←mul_sub,norm_mul]
  by_cases hx:x∈tsupport (φ:Points 2→ℂ)
  · exact mul_le_mul_of_nonneg_left (bound x hx) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero,zero_mul,zero_mul]

private theorem zero_jet (A B : Points 2→ℂ) (x : Points 2) :
    dist (iteratedFDeriv ℝ 0 A x) (iteratedFDeriv ℝ 0 B x)=‖A x-B x‖ := by
  rw [dist_eq_norm,show iteratedFDeriv ℝ 0 A x-iteratedFDeriv ℝ 0 B x=iteratedFDeriv ℝ 0 (A-B) x from by ext z;simp,
    norm_iteratedFDeriv_zero]
  rfl

include H in
theorem measured_limit (lead : Leading F J) (φ : Test 2) :
    Tendsto (fun r=>φ.applyTo (measured F none (J r) (legs w) r)) trail (𝓝 (φ.applyTo (reading C w))) := by
  rw [Metric.tendsto_nhds]
  intro ε he
  let mass:=∫x,‖φ x‖
  have hm : 0 ≤ mass:=integral_nonneg fun _=>norm_nonneg _
  let η:=ε/(2*(mass+1))
  have positive : 0<η:=div_pos he (by positivity)
  have cost : mass*η<ε := by
    dsimp [η]; rw [←mul_div_assoc]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [he,mul_nonneg hm he.le]
  have close:=Metric.tendstoUniformlyOn_iff.mp
    (lead.lead 2 (fun _=>4) (legs w) 0 _ φ.hasCompactSupport φ.tsupport_subset) η positive
  filter_upwards [close,self_mem_nhdsWithin] with r hr rp
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ cost
  apply price
  · apply φ.smearing
    let tags : Fin 2→S.Tag:=fun i=>⟨4,J r 4 (legs w i)⟩
    exact (S.class_smooth S F.room.kernel.smooth tags).continuousOn.comp (by fun_prop)
      (fun _ hz=>Work.A05.smul_conf rp hz)
  · exact φ.smearing (((Bel C.book).smooth_read H.smooth _).continuousOn)
  intro x hx
  have pt:= (hr x hx).le
  rw [zero_jet,free H w (φ.tsupport_subset hx)] at pt
  rwa [norm_sub_rev] at pt

theorem original (lead : Leading F J) {P : ℝ→change S 4} (same : ∀ᶠr in trail,J r 4=P r)
    (cent : ∀ᶠr in trail,AlignV F.room.kernel F.sector H (P r)) (φ : Test 2) :
    Tendsto (fun r=>WilsonInvariantActionPairCovariance.tested (J r 4 (stepField C))
      (J r 4 ((Bel C.book).project 4 w)) r φ) trail (𝓝 (φ.applyTo (reading C w))) := by
  apply (measured_limit F J H w lead φ).congr'
  filter_upwards [same,cent] with r hj ha
  have centered : centering S 4 (J r 4 (stepField C))=J r 4 (stepField C) := by
    rw [value_center,hj,ha.cent,sceneV H,zero_smul,sub_zero]
  unfold WilsonInvariantActionPairCovariance.tested covariance
  simp_rw [centered,placed]
  apply congrArg φ.applyTo
  funext x
  change S.classMoment S (fun _=>4) (r•x) (fun i=>J r 4 (legs w i))=_
  congr 1
  funext i
  fin_cases i <;> rfl

end YM.Integration.WilsonInvariantActionPairLimit
