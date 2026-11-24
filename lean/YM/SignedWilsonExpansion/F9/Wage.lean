import YM.SignedWilsonExpansion.F9.Empathy
/-!
# PolyCost-O and post-precision use on cohorts
Over any delivered Filter. Notation U/∆ has two uses:
- Y boarding cost powers (polynomial in log |g|)
- M_K accounting cost (subpower in |g|). Raise to second only when ready.
Keep sign projection bounds needing Y. No uniform O in order.
-/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission
open Filter Function Set Metric Asymptotics WilsonCoeffUV.Bank
open scoped Topology ContDiff BigOperators Classical
variable {ι σ η E K R T:Type*}
variable {L:Filter ι}{u g x B Y:ι→ℝ}
section counts
variable [Norm E][NormedAddCommGroup K]
abbrev Wage (L:Filter ι)(u B:ι→ℝ)(x:ι→E) := ∃ n:ℕ,x=O[L] (fun i=> (u i)^n*B i)
variable {p t:ι→E}{q q':ι→K}
lemma billed_wage (h:Billed L u p): Wage L u 1 p:= by
    obtain ⟨c,f⟩:=h; refine ⟨c.d,IsBigO.of_bound c.x (?_)⟩; filter_upwards [f] with i hi; change ‖_‖≤ c.x*‖u i ^ c.d * (1:ℝ)‖; rw [mul_one]; exact hi.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (zero_le_one.trans c.good))
lemma Wage.rise (hx:Maxer L u){n m:ℕ}(h:n≤m) (u':p=O[L] fun i=> u i^n*B i) : p=O[L] fun i=> u i^m*B i:= by
    apply u'.trans; refine IsBigO.of_bound' (hx.mono fun i hi=>?_); simp only [norm_mul,norm_pow,Real.norm_of_nonneg (zero_le_one.trans hi)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hi h) (norm_nonneg _)
namespace Wage
lemma clip (h:Wage L u B p)(w:B=O[L] g): Wage L u g p:=by
   obtain ⟨n,h⟩:=h; exact ⟨n,h.trans (IsBigO.mul (isBigO_refl _ L) w)⟩
lemma enroll (h:p=O[L] B): Wage L u B p:= ⟨0,h.congr_right (by simp)⟩
lemma fix (w:Wage L u B p)(h:p =ᶠ[L] t) (hp:B =ᶠ[L] g): Wage L u g t:= by obtain ⟨n,w⟩:=w; exact ⟨n,w.congr' h (hp.mono fun i hi=>congr_arg (u i ^ n*·) hi)⟩
lemma ascend (w:Wage L u B p)(h:Wage L u g B): Wage L u g p:=by
   obtain ⟨n,w⟩:=w; obtain ⟨m,h⟩:=h; exact ⟨n+m, w.trans (((isBigO_refl (fun i=>u i^n) L).mul h).congr_right fun i=>by rw [pow_add]; ring)⟩
lemma transfer (w:Wage L u B p)(hx:u=O[L] Y): Wage L Y B p:=by obtain ⟨n,w⟩:=w; exact ⟨n,w.trans ((hx.pow n).mul (isBigO_refl B L))⟩
lemma rel (w:Wage L u B q)(h:p=O[L] q): Wage L u B p:=by obtain ⟨n,w⟩:=w; exact ⟨n,h.trans w⟩
lemma next_zero (w:Wage L u B q)(d:∀ n:ℕ,Tendsto (fun i=> u i^n*B i) L (𝓝 0)): Tendsto q L (𝓝 0):=by obtain ⟨n,v⟩:=w; exact v.trans_tendsto (d _)
lemma spend (w:Wage L u B p)(h:∀ n:ℕ,(fun i=>u i^n*B i)=o[L] g): p=o[L] g:=by obtain ⟨n,v⟩:=w; exact v.trans_isLittleO (h n)
lemma nil : Wage L u B (0:ι→ K):= Wage.enroll (isBigO_zero ..)
lemma norm (w:Wage L u B q): Wage L u B (fun i=> ‖q i‖):=by obtain ⟨n,w⟩:=w; exact ⟨n,isBigO_norm_left.mpr w⟩
lemma plus (h:Maxer L u)(v: Wage L u B q)(w: Wage L u B q'): Wage L u B (fun i=> q i + q' i):= by
    obtain ⟨n,v⟩:=v; obtain ⟨m,w⟩:=w; exact ⟨n+m, IsBigO.add ( Wage.rise h (Nat.le_add_right ..) v) ( Wage.rise h (Nat.le_add_left ..) w)⟩
lemma neg (v:Wage L u B q): Wage L u B (fun i=> -(q i)):=by obtain ⟨n,v⟩:=v; exact ⟨n,v.neg_left⟩
lemma minus (h: Maxer L u)(v: Wage L u B q)(w: Wage L u B q') : Wage L u B (fun i=> q i- q' i):=by simp only [sub_eq_add_neg]; exact Wage.plus h v w.neg
lemma sum (h:Maxer L u)(y:ι→σ→K)(S:Finset σ)(p:∀ i∈ S,Wage L u B (fun j=> y j i)): Wage L u B (fun i=>∑ j∈ S,y i j):=by
   induction S using Finset.induction_on with
   | empty=> simp; exact nil
   | @insert i S hi ih=> simp only [Finset.sum_insert hi]; exact Wage.plus h (p i (Finset.mem_insert_self ..)) (ih (fun j hv=> p j (Finset.mem_insert_of_mem hv)))
lemma unitC (c:K) : Wage L u 1 (fun _=>c):= Wage.enroll (isBigO_const_const _ one_ne_zero _)
end Wage
end counts
section product
variable [NormedField R][NormedAddCommGroup E][NormedSpace R E]{e f:ι→ R}
namespace Wage
lemma mul (v: Wage L u B e)(w: Wage L u Y f) : Wage L u (B*Y) (fun i=> e i*f i):=by obtain ⟨n,v⟩:=v; obtain ⟨m,w⟩:=w; exact ⟨n+m,(v.mul w).congr (fun i=> rfl) (fun i=> by rw [pow_add]; exact mul_mul_mul_comm ..)⟩
lemma prod (P:σ→ι→R)(S:Finset σ)(X:σ→ι→ℝ)(p:∀ i∈S,Wage L u (X i) (P i)): Wage L u (∏ j∈ S,X j) (fun i=>∏ j∈ S,P j i):=by
    induction S using Finset.induction_on with
    | empty=> simp; exact unitC 1
    | @insert j s v ih=> simp only [Finset.prod_insert v]; exact Wage.mul (p _ (Finset.mem_insert_self ..)) (ih (fun i hi=>p i (Finset.mem_insert_of_mem hi)))
lemma power (v:Wage L u B e)(n:ℕ):Wage L u (fun i=> B i^n) (fun i=>e i^n):=by
    induction n with
    | zero=> simp; exact unitC _
    | succ n ih=> simp only [pow_succ]; exact Wage.mul ih v
lemma prodF (P:σ→ι→R)(S:Finset σ)(X:σ→ι→ℝ)(p:∀ i∈S,Wage L u (X i) (P i)): Wage L u (fun i=>∏ j∈ S,X j i) (fun i=>∏ j∈ S,P j i):=by
    simpa only [← Finset.prod_apply] using Wage.prod P S X p
lemma smul {f:ι→ E}(v: Wage L u B e)(w: Wage L u Y f) : Wage L u (B*Y) (fun i=> e i • f i):=by
    obtain ⟨n,v⟩:=v; obtain ⟨m,w⟩:=w; refine ⟨n+m,(?_)⟩; apply isBigO_norm_left.mp; simp_rw [norm_smul]; exact (( IsBigO.mul (isBigO_norm_left.mpr v) (isBigO_norm_left.mpr w))).congr_right (fun i=> by rw [pow_add]; exact mul_mul_mul_comm ..) -- LHS norm left
end Wage
end product
end YM.SignedWilsonExpansion.Commission
