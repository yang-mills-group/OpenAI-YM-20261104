import YM.Pert.Triangle.ThreeTest
/-!
The numerical triangle coefficient for an admissible signed smooth profile. Uses exactly the fields
b_F(z), U(x), U(y) of Operators.lean and the reduced convolution and local-completion factors,
with the `Subtracted` single-line read. **Does not yet identify this number with any regulator limit.**
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
variable {G:Gauge} (h:G.Simple)
local notation "P" => Points 3
local notation "I" => Fin 3

def conventionRadius := max (max (100:ℝ) (Classical.choose choose_config)) 128 + 2
lemma conventionLarge : max 100 (Classical.choose choose_config) < conventionRadius-1 := by unfold conventionRadius; linarith [le_max_left (max (100:ℝ) (Classical.choose choose_config)) 128]
lemma conventionSeparate : 128 ≤ conventionRadius := by unfold conventionRadius; linarith [le_max_right (max (100:ℝ) (Classical.choose choose_config)) 128]
def testReal : RealTest 3 := voter conventionRadius conventionSeparate
-- convention unit response signed so positive
def profileChoice : Test 3 := ⟨fun p=>(↑(stamp * testReal p):ℂ), Complex.ofRealCLM.contDiff.comp (contDiff_const.mul testReal.contDiff), by convert! testReal.hasCompactSupport; unfold HasCompactSupport tsupport; rw [show (support (fun p:P=>(↑(stamp * testReal p):ℂ))) = support testReal by ext x;simp [support,stamp_ne]], by intro p; change p∈tsupport _ → p∈conf 3; rw [tsupport,show (Function.support _ : Set P)=support testReal by ext x;simp [support,stamp_ne]];exact fun hp=>testReal.tsupport_subset hp⟩

lemma real_rotation (K:E4≃ₗᵢ[ℝ]E4) (p:P) :
    testReal (WithLp.toLp 2 (fun j:I=>K (p j)))=testReal p := by
  change candid _ (WithLp.toLp ..)=_
  unfold candid
  simp only [WithLp.ofLp_toLp,K.norm_map]
  rfl
lemma sign_region {p:P} (hp : p∈ tsupport testReal) :
    0 < ‖p 0‖^12 * (stamp * classified (p 1) (p 2) (p 0)) ∧ |‖p 0‖^12 * (stamp * classified (p 1) (p 2) (p 0))| ≤ |stamp^2| + 1 := by
       have hx:=closed_pallet conventionSeparate (a:=p) hp
       let K := Classical.choose choose_config
       have he:suitable (max (100:ℝ) K) p := ⟨hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2,by linarith [conventionLarge,hx.1]⟩
       have hu:=Classical.choose_spec choose_config
       have hK : K≤‖p 0‖ := (le_max_right ..).trans he.2.2.2
       rw [← mul_assoc]
       change 0 < scorer K p ∧ |scorer K p| ≤ _
       rw [clock_score K p he]
       exact hu _ hK _ (clock_clear _ p he (le_max_left ..))
def response (G : Gauge) (p:P) := stamp * fullTransfer G p
set_option maxHeartbeats 1400000 in
include h in
lemma cost_response {p:P} (hP : p∈tsupport testReal) :
     0 < response G p ∧ ‖response G p‖ ≤ (6*∑ a:G.ColorIndex,∑ b,∑ c,colorF a b c^2) * (|stamp^2|+1) := by
  obtain ⟨hx,hz⟩:=sign_region hP
  have H:=structure_price h
  have hz' : 1 ≤ ‖p 0‖ := by have hh := closed_pallet conventionSeparate (a:=p) hP; linarith [hh.1,conventionLarge,conventionSeparate]
  have hPos : 1 ≤ ‖p 0‖^12 := one_le_pow₀ hz'
  unfold response fullTransfer detector
  constructor
  · rw [mul_left_comm]
    rw [mul_pos_iff_of_pos_left (by positivity : 0 < ‖p 0‖^12)] at hx; exact mul_pos (by positivity) hx
  rw [mul_left_comm, norm_mul,Real.norm_of_nonneg (by linarith : 0 ≤ 6* ∑ a:G.ColorIndex,∑ b, ∑ c, colorF a b c^2)]
  gcongr
  exact (le_mul_of_one_le_left (norm_nonneg _) hPos).trans ((by simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ‖p 0‖^12)] using hz))
include h in
lemma payoff : Integrable (fun p:P=>testReal p * response G p) volume := by
  let T: Set P:=tsupport testReal
  let z := T.indicator (response G)
  have hz : ∀ᵐ p ∂(volume:Measure P), ‖z p‖ ≤ (6*∑ a:G.ColorIndex,∑ b,∑ c,colorF a b c^2) * (|stamp^2|+1) := Eventually.of_forall (fun p=> by
    by_cases hp : p∈T
    simpa only [z,indicator_of_mem hp] using (cost_response h hp).2
    exact by rw [show z p=0 from indicator_of_notMem hp _,norm_zero]; have ht' := structure_price h; positivity)
  have ht : Integrable testReal volume := testReal.contDiff.continuous.integrable_of_hasCompactSupport testReal.hasCompactSupport
  convert! ht.mul_bdd (((fullMeasurable G).const_mul stamp).indicator (isClosed_tsupport _).measurableSet).aestronglyMeasurable hz using 1
  ext p
  by_cases hp : p∈T; rw [indicator_of_mem hp];rfl; rw [show testReal p=0 from image_eq_zero_of_notMem_tsupport hp,zero_mul,zero_mul]
include h in
lemma firstTestPositive : 0 < ∫ p:P,testReal p * response G p := by
  let s := Function.support testReal
  have hs : IsOpen s := testReal.continuous.isOpen_support
  have hb : s.Nonempty := by
    let p : P:= WithLp.toLp 2 ![radial conventionRadius along, (12:ℝ) • along, (0:E4)]
    have hp :p∈s := by
      have h(z:ℝ) (hz : 0≤z) : ‖radial z along‖=z := by rw [radial,norm_smul,Real.norm_of_nonneg hz,along_norm,mul_one]
      unfold s; change candid _ p ≠0
      dsimp only [candid,p,WithLp.ofLp_toLp, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      have hx : bellM (0:ℝ) = 1 := bellM.one_of_mem_closedBall (mem_closedBall_self bellM.rIn_pos.le)
      change bellM (‖radial _ along‖^2-conventionRadius^2) * (bellM (‖radial 12 along‖^2-12^2)) * (bellM (‖(0:E4)‖^2)) ≠0
      rw [h _ (conventionSeparate.trans' (by norm_num)), h _ (by norm_num : (0:ℝ)≤12), norm_zero, sub_self, sub_self,zero_pow (by decide : (2:ℕ)≠0),hx]
      norm_num
    exact ⟨p,hp⟩
  have H (p) (hu:p ∈s) : 0 < testReal p * response G p := mul_pos (candidPositive p conventionRadius hu) (cost_response h (subset_closure hu)).1
  have he (p:P) : 0 ≤ testReal p * response G p := if hp:p∈s then (H p hp).le else by rw [show testReal p=0 from notMem_support.mp hp,zero_mul]
  exact lt_of_le_of_ne (integral_nonneg he) (fun hw=> (hs.measure_ne_zero _ hb) (measure_mono_null (t:={p|testReal p*response G p≠0}) (fun p hp=>(H p hp).ne') (mem_ae_iff.mp ((integral_eq_zero_iff_of_nonneg he (payoff h)).mp hw.symm))))

def cTest (G : Gauge) := profileChoice.applyTo (fun p=>↑(fullTransfer G p))
include h in
lemma diagnosticNonzero : cTest G ≠ 0 := by
  unfold cTest Test.applyTo
  simpa only [show ∀ p:P,profileChoice p * _ = (Complex.ofRealCLM (testReal p * response G p)) from fun p=>by change (↑(stamp * testReal p):ℂ) * (↑(fullTransfer G p)) = (↑(testReal p*response G p):ℂ); unfold response;push_cast; ring,Complex.ofRealCLM_apply, integral_complex_ofReal,ne_eq,Complex.ofReal_eq_zero] using (firstTestPositive h).ne'
end YM.Pert.Triangle
