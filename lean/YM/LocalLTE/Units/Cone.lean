import YM.LocalLTE.Units.Vain
import YM.LocalLTE.Units.Edge
/-! Radial aperture region fuel, quantitative. Inspired by boundary crossing in Ebb. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Frond Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {G:Gauge}{c L:Side}{r T M t p:ℝ} {B:BudgetPoint}
lemma launch_rad {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : ℝ→E} (h : ∀ i∈ Icc (0:ℝ) 1, Brush 2 T p X i) (hp:‖X 1-X 0‖≤ t) (hz: 2*(T*p^2)≤ r){x:ℝ}(hx:x∈ Icc (0:ℝ) 1): ‖X x-X 0‖≤ x*t+(1-x)*r:= by
  let D:=X 1-X 0; let K:=T*p^2; let Z (t:ℝ):= fderiv ℝ X t; let g (x:ℝ):= X x-x • D; let f x:= X x-Z 1 x
  have hv i (hi:i∈ Set.Icc (0:ℝ) 1): DifferentiableAt ℝ X i := (h i hi).smooth.differentiableAt (by norm_num)
  have h₀:(0:ℝ)∈ Icc (0:ℝ) 1:= ⟨le_rfl,zero_le_one⟩; have h₁:(1:ℝ)∈ Icc (0:ℝ) 1:= ⟨zero_le_one,le_rfl⟩
  have hf i (hi:i∈Set.Icc (0:ℝ) 1) : ‖Z i-Z 1‖ ≤ K := by
    have hc i (hi:i∈Set.Icc (0:ℝ) 1): ContDiffAt ℝ 1 Z i:= (h i hi).smooth.fderiv_right (by norm_num)
    have hj i (hi:i∈Set.Icc (0:ℝ) 1): ‖fderiv ℝ Z i‖ ≤ K:= by rw [← norm_iteratedFDeriv_one]; exact (norm_iteratedFDeriv_fderiv).symm.symm.trans_le ((h i hi).order 2 le_rfl)
    have hb:= (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (hc i hi).differentiableAt (by norm_num)) hj h₁ hi
    exact hb.trans (mul_le_of_le_one_right (mul_nonneg (h _ hi).nonneg (sq_nonneg _)) (by rw [Real.norm_of_nonpos (sub_nonpos.mpr hi.2)]; linarith only [hi.1]))
  have hg : ‖D-Z 1 1‖≤ K := by
    have he i (hi:i∈Set.Icc (0:ℝ) 1) : HasFDerivAt f (Z i-Z 1) i := ((hv i hi).hasFDerivAt).sub ((Z 1).hasFDerivAt)
    have ht := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_fderiv_le (fun i hi=>(he i hi).differentiableAt) (fun i hi=> (he i hi).fderiv.symm ▸ hf i hi) h₀ h₁
    simp only [f,map_zero,sub_zero,norm_one,mul_one] at ht; rwa [sub_right_comm] at ht
  have hh i (hi:i∈Icc (0:ℝ) 1): HasDerivAt g (Z i 1-D) i:= by simpa only [one_smul] using! ((hv i hi).hasFDerivAt.hasDerivAt.sub (((hasDerivAt_id' i).smul_const D)))
  have he i (hi:i∈Icc (0:ℝ) 1): ‖fderiv ℝ g i‖≤ r := by
    rw [← norm_deriv_eq_norm_fderiv, (hh i hi).deriv]; have hu : ‖Z i 1-Z 1 1‖≤ K:= by refine (le_trans (b:=‖Z i-Z 1‖*‖(1:ℝ)‖) ?_ (by simp [hf i hi])); exact (Z i - Z 1).le_opNorm _
    exact (norm_sub_le_norm_sub_add_norm_sub _ (Z 1 1) _).trans ((add_le_add hu ((norm_sub_rev ..).trans_le hg)).trans (by simpa [two_mul] using hz))
  have hp':= (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (hh i hi).differentiableAt) he h₁ hx
  rw [Real.norm_of_nonpos (sub_nonpos.mpr hx.2),neg_sub,mul_comm] at hp'
  have he : X x-X 0=x • D+(g x-g 1):= by unfold D g; simp only [D,one_smul]; abel
  rw [he]; refine (norm_add_le ..).trans (add_le_add ?_ hp'); rw [norm_smul,Real.norm_of_nonneg hx.1]; exact mul_le_mul_of_nonneg_left hp hx.1

open FrameBox.Grove
lemma thick (G:Gauge) (i:ℕ) : ∃ b:ℝ,0≤b ∧ ∀ (c:Side)(z:Directions G c),‖z‖≤1→ Mode FrameBox.Grove.soloV z i b:=by
  obtain ⟨C,hC,H⟩:= expCost G i 1
  refine ⟨(1+i.factorial*C)*((1+1)*1),?_,?_⟩; · positivity
  intro c z hz; refine ⟨by positivity,fun k=>?_⟩
  let P : Directions G c→L[ℝ] G.Color:= ContinuousLinearMap.proj k
  have hs:P z=z k:=rfl; have hy:‖P z‖≤1:=(norm_le_pi_norm z k).trans hz
  have he : Brush i 1 1 P z:=Brush.linearB P hy (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y=> by rw [one_mul,one_mul]; exact norm_le_pi_norm y k) zero_le_one
  exact thicken (f:=fun i=> G.lieExp (P i)) (he.pine (H _ hy))

lemma bend (x:Directions G c)(i:Pressure.Cell c) (H:∀ x:Directions G c,‖x‖≤1 → Mode FrameBox.Grove.soloV x 2 T) (h:‖x‖≤1):
    Brush 2 (royalty G) (4*(T*royalty G)) (fun y=>G.mat (faceValue (soloV y) i)) x:=by
  have ht:= H x h; convert tour (U:=fun x=>soloV x) (square i.2.val.1 i.2.val.2) i.1 ht.pos ht.atLink using 1
  rw [show (square i.2.val.1 i.2.val.2).length=4 from rfl]; norm_num
  rfl
lemma swell (x:Directions G c)(i:Pressure.Cell c) (H:∀ x:Directions G c,‖x‖≤1 → Mode FrameBox.Grove.soloV x 2 T) (h:‖x‖≤r)(hr:r≤1)(_hp:0≤M)(ht:2*royalty G*(4*(T*royalty G)*r)^2≤M*royalty G) {a:ℝ}(he:toll (soloV x) i ≤a) (f:ℝ) (hf:f∈Icc (0:ℝ) 1) : toll (soloV (f • x)) i ≤ f*a+(1-f)*M := by
  let P:ℝ→L[ℝ] (Directions G c) := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  have hh :‖P‖≤r:= ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans h) (fun y=> by change ‖y • x‖≤_; rw [norm_smul,mul_comm r]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _))
  let X (b:ℝ):=G.mat (faceValue (soloV (P b)) i); have hR:0<royalty G:= zero_lt_one.trans_le (royalty_ge _)
  have hv (b:ℝ) (hb:b∈Icc (0:ℝ) 1):Brush 2 (royalty G) (4*(T*royalty G)*r) X b:=by
    apply Brush.reading P (bend _ i H ?_) hh; change ‖b • x‖≤_; rw [norm_smul,Real.norm_of_nonneg hb.1]; exact (mul_le_of_le_one_left (norm_nonneg _) hb.2).trans (h.trans hr)
  have he' b : ‖X b-X 0‖= toll (soloV (b • x)) i *(royalty G):=by
    simp only [X,map_zero,show soloV (0:Directions G c)=(1:Config G c) from (by funext j; exact G.mat_lieExp_zero)]
    rw [show faceValue (1:Config G c) i=1 from by simp [faceValue, square, travel, Lattice.Step.read,posDir,negDir],G.mat_one]; exact (div_mul_cancel₀ _ hR.ne').symm
  have hη := launch_rad hv (t:= a*royalty G) (by rw [he',one_smul]; exact mul_le_mul_of_nonneg_right he hR.le) (r:= M*royalty G) (by rwa [← mul_assoc] -- edit
   ) hf
  rw [he'] at hη; exact (mul_le_mul_iff_left₀ hR).1 (hη.trans_eq (by ring)) -- edit
-- actual wedge, even composition contracts
lemma edging (G:Gauge):∃ b C:ℝ,0<b ∧ 0<C ∧ ∀ (c:Side)(P:BudgetPoint)(u r:ℝ)(F: Directions G c→L[ℝ] Directions G c)(x:Directions G c),0<u→ u≤1 → ‖x‖<r→ r≤1→ b*P.threshold < r → C*r^2 < P.threshold → (∀ x,‖F x‖≤‖x‖) → soloV (F x) ∈ sunny P → ∀ y, Dart ((-u) • x) (u*(b*P.threshold)) y → ‖y+x‖<r ∧ soloV (F (y+x))∈ sunny P:=by
  obtain ⟨s,hS,H⟩:= thick G 2
  let A:=1+4*(s*royalty G); have hR:0<royalty G:= zero_lt_one.trans_le (royalty_ge _)
  have hA:0<A:= add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
  let b:=1/(4*A); let C:=4*(4*(s*royalty G))^2 +1; have hb:0<b:=by unfold b; positivity
  refine ⟨b,C,hb,by unfold C; positivity,?_⟩
  intro c P u r F x hu hu₁ hr hR' ht hp hf hv y h
  obtain ⟨z,⟨hz,hZ⟩,hx⟩:= h
  let q:=y-z • ((-u) • x); let l:=z*u; let p:= (1-l) • x
  have he:y+x=q+p := by unfold q p l; rw [neg_smul,smul_neg, sub_smul,one_smul,mul_smul]; abel -- edit
  have hl:0≤l:=mul_nonneg hz hu.le; have h₁:l≤1:=mul_le_one₀ hZ hu.le hu₁; have hP :‖p‖=(1-l)*‖x‖:= by unfold p; rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr h₁)]
  have ha : ‖q‖ ≤ l*(b*P.threshold):=by unfold q l; rw [mul_assoc]; exact hx
  by_cases hi:l=0
  · have hq:q=0:=norm_le_zero_iff.mp (ha.trans (by simp [hi])); rw [he,hq,zero_add,show p=x from by simp [p,hi]]; exact ⟨hr,hv⟩
  have hi:0<l:=lt_of_le_of_ne hl (Ne.symm hi)
  have hi':‖y+x‖<r:= calc
    _ = ‖q+p‖:= congr_arg _ he
    _ ≤ ‖q‖+(1-l)*‖x‖:= (norm_add_le ..).trans_eq (by rw [hP])
    _ < l*r+(1-l)*r:= add_lt_add_of_lt_of_le (ha.trans_lt (mul_lt_mul_of_pos_left ht hi)) (mul_le_mul_of_nonneg_left hr.le (sub_nonneg.mpr h₁))
    _ = r:= by ring
  refine ⟨hi',fun i=>?_⟩
  have ht : 2*royalty G*(4*(s*royalty G)*r)^2≤P.threshold/2*royalty G:=by
    refine le_trans (b:=C*r^2/2*royalty G) ?_ (by gcongr)
    unfold C; nlinarith only [mul_nonneg hR.le (sq_nonneg r)]
  have hm : (1-l)∈Icc (0:ℝ) 1:=⟨sub_nonneg.mpr h₁,by linarith⟩
  have hs:toll (soloV (F p)) i ≤ (1-l)* P.threshold + l*(P.threshold/2):= by
    unfold p; rw [map_smul]; have hf':‖F x‖≤r:=(hf x).trans hr.le; convert swell _ i (H c) hf' hR' (half_pos P.threshold_pos).le ht ((hv i).le) _ hm using 2; ring
  change toll (soloV (F (y+x))) i < _
  let f':= fun a:Directions G c=> G.mat (faceValue (soloV a) i); have hy k (hy:k∈closedBall (0:Directions G c) 1):Brush 2 (royalty G) (4*(s*royalty G)) f' k:=bend k i (H c) (mem_closedBall_zero_iff.mp hy)
  let V' := F (y+x); have hσ:= (convex_closedBall (0:Directions G c) 1).norm_image_sub_le_of_norm_fderiv_le (f:=f') (fun k hk=> (hy _ hk).smooth.differentiableAt (by norm_num)) (C:=royalty G*(4*(s*royalty G))) (fun k hk=>by simpa only [normJ,norm_iteratedFDeriv_one,pow_one] using (hy _ hk).order 1 (by omega)) (mem_closedBall_zero_iff.mpr ((hf p).trans (le_trans (by rw [hP]; exact mul_le_of_le_one_left (norm_nonneg _) hm.2) (hr.le.trans hR')))) (mem_closedBall_zero_iff.mpr ((hf (y+x)).trans (hi'.le.trans hR')))
  have he : ‖V'-F p‖≤ l*(b*P.threshold) := by unfold V'; rw [he,map_add,add_sub_cancel_right]; exact (hf _).trans ha
  have hσ' : ‖f' V'-f' (F p)‖≤royalty G*A*(l*(b*P.threshold)):= hσ.trans (mul_le_mul (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hR.le) he (norm_nonneg _) (mul_nonneg hR.le hA.le))
  change ‖f' V'-1‖/(royalty G)< P.threshold; rw [div_lt_iff₀ hR]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (f' (F p)) _).trans_lt ((add_le_add hσ' ((div_le_iff₀ hR).1 hs)).trans_lt ?_); unfold b; field_simp; nlinarith only [mul_pos hi P.threshold_pos]
end YM.LocalLTE.Cabana
