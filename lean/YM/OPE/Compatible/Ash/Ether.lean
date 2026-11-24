import YM.OPE.Compatible.Ash.Fert
/-! # Uniform cap
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {n:Side}{B s q t:ℝ}{j k:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
lemma peel {s:ℝ}(hs:0<s)(F:ℝ→ E)(hk:0<k)(hB:0≤B)(H:∀ i<j, ‖F (2*(2^i*s))-F (2^i*s)‖≤B/(2^i*s)^k): ‖F (2^j*s)-F s‖≤2*(1-(1/2:ℝ)^j)*(B/s^k):=by
   induction j with
   | zero=>simp
   | succ j ih=>
     let S:=(2:ℝ)^j*s
     have he:2^j*s=S:=rfl; have hh:2^(j+1)*s=2*S:=by rw [pow_succ,←he];ring
     rw [hh,show F (2*S)-F s=(F (2*S)-F S)+(F S-F s) from by abel]
     have hp:0 ≤ B/s^k:=by positivity
     refine ((norm_add_le ..).trans (add_le_add (H j (by omega)) (ih (fun i hi=> H i (by omega))))).trans ?_
     have ht: B/(2^j*s)^k ≤ ((1/2:ℝ)^j)*(B/s^k):=by -- advance
       rw [mul_pow]; grw [← show 2^j ≤ ((2:ℝ)^j)^k from by simpa only [pow_one] using! (pow_le_pow_right₀ (a:=(2:ℝ)^j) (one_le_pow₀ (by norm_num)) (show 1 ≤ k from hk))]; exact le_of_eq (by rw [one_div,inv_pow]; field_simp)
     apply le_trans (add_le_add_left ht _); exact le_of_eq (by rw [pow_succ]; ring)
lemma steel {r:ℝ}(hr:0<r)(hk:k>0)(D:List Axis):
 let m:=D.length+2+k
 ∃ B≥0,∀ (n:Side)(s:ℝ),0<s→ turn*((m:ℝ)+1)≤s → dew n*s≤1→ mesh n*m≤1/2 →∀ (i:Axis)(z:Site n),r≤‖char (step i) z-1‖→
   ‖outsideP (dew n) s D z‖≤ B/s^k:=by
   intro m; obtain ⟨B,hB,L⟩:=roof_priced r hr D k; refine ⟨3*B,by positivity,fun n s hs hx ht h i z hz=>?_⟩
   by_cases hp:1/2 ≤ dew n*s; · exact ((L n s hs hx ht h i z hz).2 hp).trans (by gcongr; linarith)
   have hv:=dew_pos n; obtain ⟨q,hq⟩:=threshold hs hv (le_of_not_ge hp); let S:=(2:ℝ)^q*s; have he(j:ℕ):0<(2:ℝ)^j*s:=by positivity
   have ha(j:ℕ)(hj:j≤q): dew n*(2^j*s) ≤ 1:= by rw [←mul_assoc]; grw [show (2:ℝ)^j ≤ 2^q from pow_le_pow_right₀ (by norm_num) hj]; exact hq.2
   have ho(j:ℕ):s ≤ (2:ℝ)^j*s:=by grw [← one_le_pow₀ (n:=j) (by norm_num : (1:ℝ) ≤ 2)]; simp
   have H(j:ℕ)(hj:j≤ q):=L n (2^j*s) (he j) (le_trans hx (ho _)) (ha j hj) h i z hz
   have hb(j:ℕ)(hj:j<q):= (H j hj.le).1
   let F:=fun t:ℝ=> piece (dew n) t D z
   have hc:‖outsideP (dew n) S D z‖ ≤ B/s^k:= le_trans ((H q le_rfl).2 (by rw [← mul_assoc]; exact hq.1)) (by gcongr; exact ho _)
   have hi := peel hs F hk hB hb
   rw [show outsideP (dew n) s D z = (F S-F s)+outsideP (dew n) S D z from by rw [sub_add_eq_add_sub]; unfold F; rw [← clear_joint, clear_joint _ s]; ring]
   apply (norm_add_le _ _).trans ((add_le_add hi hc).trans ?_); rw [mul_div_assoc]; nlinarith only [show 0≤(1/2:ℝ)^q*(B/s^k) from by positivity]
lemma glide_add (f g:ℕ→E): glide q k (f+g) j= glide q k f j+glide q k g j:=by
   induction k generalizing j with
   | zero=>rfl
   | succ k ih=> change glide q k _ _- q^k•glide q k _ _=(glide q k _ _- q^k•_)+(glide q k _ _-q^k•_); rw [ih,ih,smul_add]; unfold glide; abel
lemma glide_neg (f:ℕ→E): glide q k (-f) j= -glide q k f j:=by
   induction k generalizing j with
   | zero=>rfl
   | succ k ih=> change glide q k _ _- q^k • glide q k _ _ = -(glide q k _ _- q^k • glide q k _ _); rw [ih,ih,smul_neg];abel
lemma sterling (q:ℝ)(k:ℕ):∃ C≥0,∀ f:ℕ→E,∀ i t, (∀ j≤ k,‖f (i+j)‖ ≤ t) → ‖glide q k f i‖ ≤ C*t:=by
   induction k with
   | zero=> exact ⟨1,zero_le_one,fun f i t h=>by simpa only [add_zero,one_mul] using! h 0 le_rfl⟩
   | succ k ih=>
     obtain ⟨C,hC,hf⟩:=ih; refine ⟨C+‖q^k‖*C,by positivity,fun f i t h=>?_⟩
     change ‖glide q k f i - q^k • glide q k f (i+1)‖≤_; grw [norm_sub_le,norm_smul,hf f i t (fun j hj=>h j (by omega)),hf f _ t (fun j hj=>by rw [add_assoc]; apply h; omega)]; exact le_of_eq (by ring)
end YM.OPE.Balsam
