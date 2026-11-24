import YM.Contacts.Tempo.Tone
namespace YM.Contacts.Tempo
open Set Filter Finset
open scoped Topology Classical BigOperators NNReal
noncomputable section
variable {n i j d k:ℕ}{κ:Type}{X:Type}{m:κ→ℕ}{P:κ→ℕ→ℝ→Prop}{b a c u:ℝ}{v g w f:κ→ℕ→ℝ}
section neutral
lemma gap_left (h:i≤j):gap j i=(j:ℝ)-(i:ℝ):= by rw [gap,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
lemma gap_right (h:i≤j): gap i j=(j:ℝ)-(i:ℝ):= by rw [gap_sym,gap_left h]
lemma toll_nn {i j x y:ℕ} (h:gap i j≤gap x y): toll i j d ≤ toll x y d:= pow_le_pow_left₀ (add_nonneg zero_le_one dist_nonneg) (add_le_add_right h 1) _ -- order left vs right
lemma stride [NormedAddCommGroup X] (f:ℕ→X) (n k:ℕ)(he:∀ i,n≤ i→i<n+k→ ‖f (i+1)-f i‖≤b) : ‖f (n+k)-f n‖ ≤ (k:ℝ)*b:= by
   induction k with|zero=> simp|succ k ih=> rw [←Nat.add_assoc, show f (_+1)-_=f (n+k+1)-f (n+k)+(f (n+k)-f n) from by abel]; exact (norm_add_le ..).trans ((add_le_add (he _ (Nat.le_add_right ..) (by omega)) (ih (fun i hi ht=> he i hi (by omega)))).trans_eq (by push_cast; ring))
lemma neutral_forward [NormedAddCommGroup X] (f:ℕ→X)(hx:0≤b)(he:∀ i, ‖f (i+1)-f i‖≤ b*toll n i d) (k:ℕ): ‖f (n+k)-f n‖ ≤ b*toll n (n+k) (d+1):= by
   let W:= toll n (n+k) d; have hw:0≤W:= (toll_glow ..).le; have h (i:ℕ)(hv:n≤ i)(ht:i<n+k) : toll n i d ≤ W:= toll_nn (by rw [gap_right hv,gap_add]; have ht':(i:ℝ)<(n:ℝ)+k:= (by exact_mod_cast ht); linarith)
   apply (stride f n k (fun i hi hv=> (he i).trans (mul_le_mul_of_nonneg_left (h i hi hv) hx))).trans; unfold toll; rw [pow_succ]; change _ ≤ b*(W*_); rw [gap_add]; nlinarith only [mul_nonneg hx hw]
lemma neutral_back [NormedAddCommGroup X] (f:ℕ→X)(k:ℕ)(hx:0≤b)(he:∀ i, ‖f (i+1)-f i‖≤ b*toll (n+k) i d) : ‖f n-f (n+k)‖ ≤ b*toll (n+k) n (d+1):= by
   let W:= toll n (n+k) d; have hw:0≤W:= (toll_glow ..).le; have h (i:ℕ)(hv:n≤ i)(ht:i<n+k) : toll (n+k) i d ≤ W:= toll_nn (by rw [gap_left ht.le, gap_add]; push_cast; have ht':(n:ℝ)≤(i:ℝ):= (by exact_mod_cast hv); linarith)
   rw [norm_sub_rev, toll_sym (n+k) n]; apply (stride f n k (fun i hi hv=> (he i).trans (mul_le_mul_of_nonneg_left (h i hi hv) hx))).trans; unfold toll; rw [pow_succ]; change _ ≤ b*(W*_); rw [gap_add]; nlinarith only [mul_nonneg hx hw]
lemma Rates.neutral (h:Rates m f)(hx:∀p, ‖v p (m p)‖≤ a)(hu:0 ≤ a)(hr:Runs 1 f v): Rates m v:= by
   obtain ⟨d,b,hb,H⟩:= h; let X (p:κ)(i:ℕ):= v p i-v p (m p); have he(p:κ)(i:ℕ): ‖v p (i+1) - v p i‖≤ b*toll (m p) i d := by rw [hr,one_mul,add_sub_cancel_left]; exact H ..
   have he'(p i): ‖X p i‖ ≤ b*toll (m p) i (d+1):= by
       rcases le_total (m p) i with hy|hy; · obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le hy; exact neutral_forward (v p) hb (he p) k
       obtain ⟨k,hk⟩:= Nat.exists_eq_add_of_le hy; unfold X; rw [hk]; exact neutral_back (v p) k hb (fun i=> hk ▸ he p i)
   refine ⟨d+1,b+a,add_nonneg hb hu,fun p i=> ?_⟩; change ‖v p i‖≤_; rw [show v p i=X p i+v p (m p) from (sub_add_cancel ..).symm, add_mul]; exact (norm_add_le ..).trans (add_le_add (he' p i) ((hx p).trans (le_mul_of_one_le_right hu (toll_good ..))))
end neutral
section contraction
variable (hc:0≤c)(ht:c<1)
abbrev cape (a:ℝ) (p n k:ℕ): ℝ:= (a+gap p n)^k
lemma folds (ha:1≤a)(i j d): toll i j d ≤ cape a i j d:= pow_le_pow_left₀ (add_nonneg zero_le_one dist_nonneg) (add_le_add_left ha _) _
lemma cap_rate (ha:1≤a)(i j d): cape a i j d≤ a^d*toll i j d:= by
   unfold toll cape; rw [←mul_pow]; apply pow_le_pow_left₀ (add_nonneg (zero_le_one.trans ha) dist_nonneg); nlinarith only [mul_le_mul_of_nonneg_right ha (gap_nn i j)]
lemma bend_lt (ha:1≤a)(h:1≤u)(hy:1≤ (u-1)*a)(p n d): cape a p n d ≤ u^d*cape a p (n+1) d := by
   unfold cape; rw [←mul_pow]; apply pow_le_pow_left₀ (add_nonneg (zero_le_one.trans ha) dist_nonneg); nlinarith only [hy,mul_le_mul_of_nonneg_right h (gap_nn p (n+1)),gap_tri p n (n+1),show gap (n+1) n=1 from by rw [gap_sym,gap_add,Nat.cast_one]]
include ht hc
lemma capmade (d:ℕ):∃ a≥1,∃ u>1,a≥(u-1)⁻¹∧c*u^d<1:= by -- continuity
    have he : ∀ᶠ u:ℝ in 𝓝 1,c*u^d < 1:= by
       let H:Continuous (fun u:ℝ=> c*u^d):= by fun_prop
       exact H.continuousAt.eventually (gt_mem_nhds (by simpa only [one_pow,mul_one] using ht))
    obtain ⟨u,h,H⟩:= Eventually.exists_gt he; exact ⟨max 1 (u-1)⁻¹,le_max_left ..,u,h,le_max_right ..,H⟩
lemma contract (hb:0≤b)(ha:0≤ a)(h:Rising P)(H:∀ p,P p 0 (a*toll (m p) 0 d))(U:∀ p i r, 0≤r→ P p i r → P p (i+1) (c*r+b*toll (m p) i d)): Road m P:= by
   obtain ⟨e,he,r,hr,hw,hU⟩:= capmade hc ht d; let t:=1-c*r^d; let V:= b*r^d; have ht':0<t:= sub_pos.mpr hU; have hr':0 < r:=lt_trans zero_lt_one hr; have hV:0≤V:= mul_nonneg hb (by positivity); let w:= a+V/t; have hw':a≤w:=le_add_of_nonneg_right (by positivity); have hu:0 ≤ w:=ha.trans hw'
   refine ⟨d,w*e^d,mul_nonneg hu (by have h:0 < e:=lt_of_lt_of_le zero_lt_one he; positivity), fun p i=>?_⟩; let Q(i:ℕ):= cape e (m p) i d; have hQ(i):= folds he (m p) i d; have hv(i:ℕ):0≤ Q i:= ((toll_glow ..).le).trans (hQ i); suffices hx:∀ i,P p i (w*Q i) by exact h _ _ _ _ ((mul_le_mul_of_nonneg_left (cap_rate he _ _ _) hu).trans_eq (mul_assoc ..).symm) (hx _)
   intro i; induction i with|zero=> exact h _ _ _ _ (mul_le_mul hw' (hQ 0) (toll_glow ..).le hu) (H p)|succ i ih=>
   have hB:V≤ w*t:= by unfold w; rw [add_mul,div_mul_cancel₀ _ ht'.ne']; exact le_add_of_nonneg_left (mul_nonneg ha ht'.le)
   have hR:(c*w+b)*r^d ≤ w:= by change b*r^d ≤ w*(1-c*r^d) at hB; nlinarith only [hB]
   let g:0≤ c*w+b:= add_nonneg (mul_nonneg hc hu) hb
   apply h _ _ _ _ _ (U p i _ (mul_nonneg hu (hv i)) ih); refine le_trans (b:=(c*w+b)*Q i) ?_ (le_trans (mul_le_mul_of_nonneg_left (bend_lt he hr.le (by rw [mul_comm]; apply ((div_le_iff₀ (sub_pos.mpr hr)).mp); rwa [one_div]) _ _ _) g) (?_: (c*w+b)*(r^d*Q (i+1)) ≤ _)); rotate_left
   · rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hR (hv _)
   rw [add_mul (c*w) b (Q i),mul_assoc c w (Q i)]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQ i) hb)
end contraction
end
end YM.Contacts.Tempo
