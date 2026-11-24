import YM.MSbar.Transfer.Remove

/-! Vanishing lemma for transfer algebra. Use **half-plane norm bounds**, no conclusions from values
at sparse dimensions of arbitrary complex analytic function. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Transfer
open Complex Metric Filter Set Function
open scoped Topology ContDiff BigOperators Classical
variable {N : ℕ} {f g : ℂ→ℂ} {M t T : ℝ}

lemma bill (ht : 1 ≤ t) (h : t<T) : ‖((t:ℂ)-T)/((t:ℂ)+T)‖ ≤ T/(T+1):= by
   rw [norm_div,← ofReal_sub,← ofReal_add,norm_real,norm_real,Real.norm_of_nonpos (sub_nonpos.mpr h.le),Real.norm_of_nonneg (by linarith : 0 ≤ t+T)]; apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
   nlinarith only [ht,h,mul_le_mul_of_nonneg_left ht (show 0 ≤ T by linarith)]

-- recurse estimates from integer start T with enough gap from t.
lemma decay_n (hf : DifferentiableOn ℂ f half)(hM : ∀ z∈half,‖f z‖ ≤ M)(h : ∀ n:ℕ, f ((T:ℂ)+n)=0)(ht : 1≤t) (he:t<T) (n:ℕ):
    ‖f (t:ℂ)‖ ≤ T/(T+n)*M:=by
    induction n generalizing f T with
    | zero =>
       have hZ : T>0:= by linarith
       specialize hM (t:ℂ) (show _ from (show 0<t from by linarith)); simpa [hZ.ne'] using hM
    | succ n ih =>
       have hz : (t:ℂ)∈half:=show 0<t from by linarith
       have hx : T>0:= by linarith
       obtain ⟨g,hg,hm,hP⟩:= price hx hf (by simpa using h 0) hM
       have hh(n:ℕ):g (↑(T+1)+n)=0:=by
          let z:ℂ:= (↑(T+1):ℂ)+n; have hN :z=((T:ℂ)+↑(n+1:ℕ)):=by unfold z; push_cast; ring
          have hp : 0< z.re-T:= by rw [hN]; simp; positivity
          have hj: z∈half:= show 0< z.re from by linarith
          have hw: f z=0:=hN ▸ h (n+1)
          exact (mul_eq_zero.mp ((hP z hj).symm.trans hw)).resolve_left (div_ne_zero (sub_ne_zero.mpr (fun ht=> by rw [ht, ofReal_re,sub_self] at hp; exact lt_irrefl _ hp)) (ball_key hx hj))
       calc
        _ = _ := congr_arg norm (hP _ hz)
        _ ≤ (T/(T+1))*((T+1)/(T+1+n)*M):=by rw [norm_mul]; exact mul_le_mul (bill ht he) (ih hg hm hh (by linarith only [he])) (norm_nonneg _) (by positivity)
        _ = _:=by push_cast; field_simp <;> ring

lemma real_zero (hf : DifferentiableOn ℂ f half)(hM : ∀ z∈half,‖f z‖ ≤ M) (h : ∀ᶠ n:ℕ in atTop,f n=0) (ht : 1≤t) : f t=0:=by
    obtain ⟨j,hj⟩:=eventually_atTop.mp h
    obtain ⟨n,H,hn⟩:= ((eventually_ge_atTop j).and (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop t))).exists
    have hB(m:ℕ):f ((↑(n:ℝ):ℂ)+m)=0:= by rw [ofReal_natCast,←Nat.cast_add]; exact hj _ (H.trans (Nat.le_add_right ..))
    apply norm_le_zero_iff.mp; apply ge_of_tendsto (show Tendsto (fun k:ℕ=>(n:ℝ)/(n+k)*M) atTop (𝓝 0) from ?_) (Eventually.of_forall (fun k=> decay_n hf hM hB ht hn k))
    exact (by simpa using (tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)).mul_const M)


lemma real_unique (hf : Differentiable ℂ f) (h : ∀ x:ℝ,T≤x→ f x=0) : f=0:=by
    apply AnalyticOnNhd.eq_of_frequently_eq (fun x _=>hf.analyticAt x) (fun _ _=>analyticAt_const) (z₀:=(↑T:ℂ)); intro he
    have hx : ∀ᶠ x in 𝓝[>] T,T < x:= self_mem_nhdsWithin
    let r:=𝓝[>] T; have hh : Tendsto (fun x:ℝ=>(x:ℂ)) r (𝓝[≠] ↑T):= tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousWithinAt,(show ∀ᶠ x:ℝ in 𝓝[>] T, (x:ℂ)≠↑T from hx.mono fun x hx=> by exact_mod_cast (show T<x from hx).ne')⟩
    obtain ⟨x,hx,hH⟩:= (hx.and (hh.eventually he)).exists
    exact hH (h x (le_of_lt hx))
end YM.MSbar.Transfer
