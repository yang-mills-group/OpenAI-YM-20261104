import YM.MS.Arc.Blanc
/-!
# Entire dimension identity

Supposing normalization and manifold analyticity (not just real d), positive integer
 $z$ dense enough. Quantitative telescoping at real $z>=1$, suffices, with bound
 polynomial * exponential in Re. Use Town since later germs/Hills. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]{z:ℂ} {C:ℝ}{f:ℂ→F}{x:ℝ}{m n k:ℕ}
lemma right_float {p:ℝ}(h:p>0): (p:ℂ)∈right0:= h
lemma fall (h:1≤x)(p:ℝ)(he:x<p) : ‖runP p (x:ℂ)‖≤ p/(p+1):= by
   unfold runP; rw [norm_div,← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, norm_of_nonneg (by linarith : 0≤x+p), Real.norm_eq_abs, abs_of_neg (sub_neg.mpr he),div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
lemma ticket (hf: Forest right0 f)(hv:∀ i∈right0,‖f i‖≤C)(hp:∀ k:ℕ,n≤k→ f k=0)(hz:1≤x)(hh:x<(n:ℝ)) (m:ℕ): ‖f x‖≤ C*n/(n+m:ℕ):= by -- parsing coerces C*n ℝ, / cast
    have hx:0<x:=by linarith
    have hn:=hx.trans hh; induction m generalizing f n with
    | zero=> simpa [hn.ne'] using hv _ (right_float hx)
    | succ m ih=> -- first n, then m with shifted n
        obtain ⟨G,hG,hQ,hL⟩:= mop hf hv (n:=(n:ℝ)) hn (by exact_mod_cast hp n le_rfl)
        have h0 (i:ℕ)(he:n+1≤ i): G i=0:= by
            have hm : (n:ℝ)<(i:ℝ):= by exact_mod_cast (Nat.lt_of_add_one_le he)
            have hε: (i:ℂ)∈right0:= by exact_mod_cast right_float (hn.trans hm) -- often not cast prop
            have hi:= hL i hε; rw [hp i (by omega)] at hi; exact (smul_eq_zero.mp hi.symm).resolve_left (thin hε hn (by exact_mod_cast (show i≠n by omega)))
        have he:= ih hG hQ h0 (lt_trans hh (by simp)) (lt_trans hn (by simp)); -- inspect
        rw [hL _ (right_float hx), norm_smul]; refine (mul_le_mul (fall hz n hh) he (norm_nonneg _) (by positivity)).trans ?_; apply le_of_eq; rw [show n+(m+1)=n+1+m by omega]; push_cast; field_simp
lemma clears (h: Forest right0 f) (hv:∀ i∈right0,‖f i‖≤ C)(hp:∀ᶠ n:ℕ in atTop, f n=0)(hx:1≤x): f (x:ℂ)=0:= by
    obtain ⟨N,hN⟩:= eventually_atTop.mp hp; obtain ⟨m,hm⟩:= exists_nat_gt x; let Z:=max N m; have hp: ∀ k, Z≤k→ f ((k:ℕ):ℂ)=0:= fun k hk=> hN k ((le_max_left ..).trans hk); have hz: x<(Z:ℝ):= lt_of_lt_of_le hm (by exact_mod_cast le_max_right N m)
    apply norm_le_zero_iff.mp; refine ge_of_tendsto ( tendsto_const_nhds (f:=(atTop:Filter ℕ)) (x:=C*(Z:ℝ)) |>.div_atTop (g:=fun i:ℕ=>(((Z+i:ℕ):ℝ))) ?_) (Eventually.of_forall fun i=> ticket h hv hp hx hz i)
    refine tendsto_atTop_mono (fun i:ℕ=> show (i:ℝ) ≤ _ by exact_mod_cast Nat.le_add_left i Z) (tendsto_natCast_atTop_atTop (R:=ℝ))
end YM.MS.Arc
