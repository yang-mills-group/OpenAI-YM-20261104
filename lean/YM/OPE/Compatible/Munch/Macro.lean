import YM.OPE.Compatible.Munch.Fir
/-! # support cost exponential closure. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset Precision Push Push.AbsoluteSums.Animals Exterior Next.Free
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Lav
variable {E I:Type*} {t s:ℝ}{G:Gauge}
lemma Tcμ (l:Filter E)(V:E→ℝ)(h:Tendsto V l atTop): RateLE l V V 0:=by
       intro r hr; have hz : 0 < r/2:= half_pos hr; filter_upwards [h.eventually_gt_atTop 0,(Real.tendsto_exp_atTop.comp (h.const_mul_atTop hz)).eventually_ge_atTop (2/r)] with i hi hp; rw [Real.norm_eq_abs,abs_of_pos hi]; let u:= r/2 * V i; change 2/r ≤ Real.exp u at hp
       calc V i =u*(2/r):=by unfold u;field_simp -- ring_nf
            _ ≤ Real.exp u*Real.exp u:=mul_le_mul (le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp u)) hp (by positivity) (Real.exp_nonneg _)
            _ = Real.exp (r*V i):=by rw [←Real.exp_add]; unfold u; ring_nf
lemma κ_growth (l:Filter E)(T:E→ℝ)(ht:Tendsto T l atTop)(n:E→ℕ)(h:RateLE l T (fun i=>(n i:ℝ)) 0): RateLE l T (fun i=>(κceil (n i):ℝ)) 0:=by
       unfold κceil ballCost; push_cast; have hx(x:ℝ):= RateLE.const x ht; let H:= ((hx 64).mul h).mono (le_of_eq (show (0:ℝ)+0=0 from by norm_num)); exact ((((H.add H ht).add (hx 1) ht).pow 4 ht).mul (hx (Fintype.card (TypeFace 1):ℝ))).mono (by norm_num) -- namespace
lemma ride_φ (G:Gauge) (C:ℝ)(n j:ℕ): RateLE atTop (fun i:ℕ=>(i:ℝ)) (fun i=> lamp_B G n i C j) 0:=by
       let T (i:ℕ):ℝ := i; have ht:Tendsto T atTop atTop:= tendsto_natCast_atTop_atTop; have hp:= Tcμ _ _ ht; have hx(i:ℝ):=RateLE.const i ht; have hz:RateLE atTop T (fun i:ℕ=>(κceil (i+1):ℝ)) 0 := κ_growth _ _ ht _ (by push_cast; exact hp.add (hx 1) ht)
       let W(j:ℕ):= (hx 1).add ((((hz.mul (hx (Fintype.card G.ColorIndex:ℝ))).mul (hx (Real.sqrt C*ampleP j))).mono (show _≤0 by norm_num))) ht
       induction n generalizing j with
       | zero=> exact RateLE.const (1:ℝ) ht
       | succ n ih=> exact ((W (2*j)).mul (ih _)).mono (by norm_num)
lemma ΘVar (ht:0 < s)(G:Gauge)(C:ℝ)(n j:ℕ):∃ D:ℝ,0 ≤ D∧∀ i:ℕ, burst s i* lamp_B G n i C j ≤ D*burst (s/2) i:=by
       let E:= lamp_B G n; let f(i:ℕ):= E i C j; let F:=burst (s/2); obtain ⟨N,hN⟩:= (eventually_atTop.1 (ride_φ G C n j (s/2) (by linarith :0 <s/2))); let D:=∑ k∈range N,‖f k * F k‖; have hz:0 ≤ D:= sum_nonneg fun _ _=> norm_nonneg _; refine ⟨1+D,by positivity,fun i=>?_⟩
       have he:burst s i=F i*F i:=by unfold F burst; rw [← Real.exp_add];ring_nf
       have hf:0 < F i:= Real.exp_pos _; rw [he,show (F i*F i) * _= (f i* F i)*F i from by ring]; apply mul_le_mul_of_nonneg_right _ hf.le; by_cases hh:N ≤ i
       · refine (mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans (hN i hh)) hf.le).trans ?_; rw [show Real.exp (s/2*(i:ℝ))*F i=1 from ?_]; · exact le_add_of_nonneg_right hz
         unfold F burst;rw [←Real.exp_add]; ring_nf; simp
       exact ((Real.le_norm_self _).trans (Finset.single_le_sum (fun x _=>norm_nonneg (f x*F x)) (mem_range.mpr (Nat.lt_of_not_ge hh)))).trans (le_add_of_nonneg_left zero_le_one)
lemma Bsum (ht:0<s)(m n:ℕ): ∑ i∈ range m, burst s (n+i:ℕ) ≤ (1-Real.exp (-s))⁻¹*burst s n:=by
        let f:= Real.exp (-s); let F(i:ℕ):= burst s i; have hf :0 ≤ f:= Real.exp_nonneg _; have hh:f<1:=by simpa only [← Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht)
        let b:=(1-f)⁻¹; have hg : 0 ≤ b:= inv_nonneg.mpr (sub_nonneg.mpr hh.le); have hb:b-f*b=1:=by rw[← one_sub_mul f b]; exact mul_inv_cancel₀ (sub_ne_zero.mpr hh.ne') -- name
        have hZ(i:ℕ): F (i+1)=F i*f:=by unfold F burst; rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one, Real.exp_add]
        have hP : b* F n=∑ i∈ range m,F (n+i)+ b*F (n+m):=by -- sum parentheses precedence
             induction m with
             | zero=> simp
             | succ m ih=> rw [ih,sum_range_succ, ←Nat.add_assoc,hZ]; nlinarith only [congr_arg (fun t=>t*(F (n+m))) hb]
        change _≤b*F n; rw [hP]; exact le_add_of_nonneg_right (mul_nonneg hg (Real.exp_nonneg _))
end YM.OPE.Borealis.Galea
