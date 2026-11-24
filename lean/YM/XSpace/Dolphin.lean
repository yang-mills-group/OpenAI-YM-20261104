import YM.XSpace.Salsa
/-!
# Summit for the contact bound
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Asymptotics Filter Set Lattice Trace Relief Sail
open scoped Topology BigOperators
variable {ι V K:Type}{L:Filter ι}{a:ι→ℝ}{i j k:ℕ}{S:ι→Cover→Prop}
variable [NormedAddCommGroup V]
section W
variable {F G:ι→Cover→V}
namespace Dance
lemma zero : Dance S L a k (fun _ _=> (0:V)):=⟨0,le_rfl, Eventually.of_forall fun _ _ _=> by simp⟩
lemma add (h:Dance S L a k F)(K:Dance S L a k G): Dance S L a k (fun i x=> F i x+G i x):=by obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,A⟩:=K; refine ⟨C+D,add_nonneg hC hD,?_⟩; filter_upwards [H,A] with i hi ht B h; exact (Finset.sum_le_sum (fun x (_:x∈B)=> norm_add_le (F i x) _)).trans (by rw [Finset.sum_add_distrib,add_mul]; exact add_le_add (hi B h) (ht B h))
lemma neg (h:Dance S L a k F):Dance S L a k (fun i x=> -F i x):=tango (B:=1) h zero_le_one (Eventually.of_forall fun _ _ _=>by simp)
lemma const_smul {K:Type*}[NormedField K][NormedSpace K V] (h:Dance S L a k F)(D:K): Dance S L a k (fun i x=> D • F i x):=tango h (norm_nonneg D) (Eventually.of_forall fun _ _ _=> le_of_eq (norm_smul ..))
lemma fin {T:Type*}(p: T→ι→Cover→V)(B:Finset T)(h:∀ i∈B,Dance S L a k (p i)): Dance S L a k (fun i x=> ∑ a∈B,p a i x):=by
  classical induction B using Finset.induction_on with | empty=> simp_rw [Finset.sum_empty]; exact zero | insert x B hx ih=> simp_rw [Finset.sum_insert hx]; exact (h x (Finset.mem_insert_self ..)).add (ih (fun w hw=> h _ (Finset.mem_insert_of_mem hw)))
lemma order (s: Stage L a)(h:i≤ k)(p:Dance S L a k F): Dance S L a i F:=by obtain ⟨C,hC,H⟩:=p; refine ⟨C,hC,?_⟩; filter_upwards [H,s.good,s.zero.eventually (ge_mem_nhds zero_lt_one)] with u hu hh hx B hB; exact (hu B hB).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hh.le hx h) (Real.sqrt_nonneg _)) hC)
lemma tax [NormedField K][NormedSpace K V]{d:ι→K}(s:Stage L a)(h:funds L a i d)(H:Dance S L a k F): Dance S L a (i+k) (fun t x=> d t • F t x):=by
  obtain ⟨C,Hc⟩:= IsBigO.bound h; obtain ⟨D,hD,h⟩:=H; refine ⟨max C 0*D,mul_nonneg (le_max_right ..) hD,?_⟩; filter_upwards [Hc,h,s.good] with t hc hh ht B hB; rw [Real.norm_of_nonneg (pow_pos ht _).le] at hc; simp_rw [norm_smul]; rw [← Finset.mul_sum]; exact (mul_le_mul (hc.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg ht.le _))) (hh B hB) (Finset.sum_nonneg fun _ _=>norm_nonneg _) (mul_nonneg (le_max_right ..) (pow_nonneg ht.le _))).trans_eq (by unfold tariff; rw [pow_add]; ring)
lemma lift (h:Dance S L a k F)(H:∀ᶠ i in L, ∀ w,F i w≠0→ S i w): Priced L a k F:=by
  obtain ⟨C,hC,K⟩:=h; refine ⟨C,hC,?_⟩; filter_upwards [K,H] with i hi hh B _; rw [← add_zero (_*tariff k (a i))]; exact phase (p:=fun w=> F i w ≠ 0) (fun W _ h=> hi W (fun w hw=> hh w (h w hw))) (fun W _ h=> le_of_eq (Finset.sum_eq_zero fun w hw=> by rw [Classical.not_not.mp (h w hw), norm_zero]))
end Dance
abbrev Little (L:Filter ι)(a:ι→ℝ)(k:ℕ)(F:ι→V): Prop:= F =o[L] fun i=> a i^k
lemma fee (h:Priced L a k F) : ∀ᶠ i in L, Summable fun x:Cover=> ‖F i x‖:=by obtain ⟨C,hC,H⟩:=h; filter_upwards [H] with i hi; exact summable_of_sum_le (fun _=> norm_nonneg _) (fun B=> hi B (fun _ _=> trivial))
lemma pull (s:Stage L a)(h:Priced L a (k+1) F): Little L a k (fun i=>∑' w:Cover,F i w):= by
  have ht(x:ℝ)(h:0<x): tariff (k+1) x= Real.sqrt x * x^k:=by unfold tariff swing; have hp:0<Real.sqrt x:=(by positivity); rw [pow_succ, Real.sqrt_inv]; field_simp; nlinarith [Real.sq_sqrt h.le, Real.mul_self_sqrt h.le]
  obtain ⟨C,hC,H⟩:= h; apply IsLittleO.of_bound; intro c hc; have he:Tendsto (fun i=> C*Real.sqrt (a i)) L (𝓝 0):=by simpa using (s.zero.sqrt).const_mul C; -- synt
  filter_upwards [H,s.good,he.eventually (ge_mem_nhds hc)] with i hi h hx; have ho (W:Finset Cover):= hi W (fun _ _=>trivial); have hp:= summable_of_sum_le (fun w=> norm_nonneg (F i w)) ho; rw [Real.norm_of_nonneg (pow_pos h _).le]; refine (norm_tsum_le_tsum_norm hp).trans ((hp.tsum_le_of_sum_le ho).trans ?_); rw [ht _ h,← mul_assoc]; exact mul_le_mul_of_nonneg_right hx (pow_nonneg h.le _)
end W
lemma tau {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{f:ι→V}(s:Stage L a)(h: Little L a k f): Tendsto (fun i=> (a i)⁻¹^k • f i) L (𝓝 0):=by
  apply Metric.tendsto_nhds.mpr; intro b hb; filter_upwards [IsLittleO.bound h (half_pos hb),s.good] with i hi ht; rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (pow_pos (inv_pos.mpr ht) k).le]; rw [Real.norm_of_nonneg (pow_pos ht _).le] at hi; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hi (pow_nonneg (inv_nonneg.mpr ht.le) _)) _; rw [inv_pow]; field_simp; norm_num
lemma loudest (c:ℝ){f:ι→V} (H:∀ s:Finset ι, ∑ i∈s,‖f i‖≤c): ‖∑' i,f i‖≤c:=(norm_tsum_le_tsum_norm (summable_of_sum_le (fun _=> norm_nonneg _) H)).trans (Real.tsum_le_of_sum_le (fun _=> norm_nonneg _) H)
end YM.XSpace.Octave
