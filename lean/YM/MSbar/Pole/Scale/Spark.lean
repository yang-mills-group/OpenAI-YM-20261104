import YM.MSbar.Pole.Scale.Through
/-! Smooth germ transverse to zero forces no scaling logarithm in a dilation
invariant singular coefficient. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Spark
open Set Function Filter MeasureTheory Polynomial Mellin Momentum Ambient Curtain
open scoped Topology ContDiff Classical BigOperators Interval
variable {I : Type} [Fintype I] {A : Finset I} {F : ℝ → Cloud I}

private def Q (P : ℂ[X]) (t : ℝ) := Polynomial.eval (t:ℂ) P

private lemma damps (P : ℂ[X]) : Tendsto (fun t:ℝ => (Real.exp (-t):ℂ)*Q P t) atTop (nhds 0) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Q,eval_add,mul_add,zero_add] using hp.add hq
  | monomial i c =>
    have he:=Complex.continuous_ofReal.continuousAt (x:=0) |>.tendsto.comp (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i)
    have hh := he.const_mul c
    rw [Complex.ofReal_zero,mul_zero] at hh
    convert hh using 1; funext r
    simp only [comp_apply,Complex.ofReal_mul,Q, eval_monomial, Complex.ofReal_pow]
    ring

private theorem polynomial (P : ℂ[X]) {k:ℂ} (h : Tendsto (Q P) atTop (nhds k)) : P=C k:= by
  -- use tendsto_cocompact?
  by_contra he
  by_cases hc : P.natDegree=0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hc] at h he
    unfold Q at h; simp only [eval_C] at h
    rw [show P.coeff 0=k from tendsto_nhds_unique tendsto_const_nhds h] at he; exact he rfl
  have hz : Tendsto (fun t:ℝ=>‖(t:ℂ)‖) atTop atTop := tendsto_atTop_mono (f:=id) (fun x=>by simpa using le_abs_self x) tendsto_id
  have ht := P.tendsto_norm_atTop (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hc)) hz
  exact not_tendsto_atTop_of_tendsto_nhds h.norm ht

variable {a:ℤ}

lemma origin (h : Ledger A a F) (r : ℝ) : Canonical (F r) := by
  induction h with
  | zero => exact ⟨⟨fun _ _ _=>rfl,fun _ _=>rfl⟩,fun _=> Packet.zero⟩
  | line k c hf =>
    let v:ℂ:= (r:ℂ)^a*(Real.log r:ℂ)^k*c
    have hb := Meridian.base (singleMove A r (R:=1) hf.constant) zero_lt_one
    refine ⟨⟨fun n J x=>congr_arg (v*·) (hb.1.moves n J x),fun n x=>congr_arg (v*·) (hb.1.agrees n x)⟩,fun n=> (Packet.const v).mul (hb.2 n)⟩
  | merge _ _ ih ih' => exact ⟨ih.1.add ih'.1,fun n=>(ih.2 n).add (ih'.2 n)⟩
private lemma cone (h:Ledger A a F) {n : ℕ} (x:External I n) :
    ∃ P:ℂ[X],∀ t : ℝ,
        F (Real.exp t) n (move A (Real.exp (-t)) x) = (Real.exp t:ℂ)^a*Q P t := by
  induction h with
  | zero => refine ⟨0,fun _=>by simp [Q]⟩
  | @line i H c hh=>
      refine ⟨C (c*H n x)*X^i,fun t=>?_⟩; dsimp only
      rw [Real.log_exp,nesting, Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos _).ne', one]; simp [Q]; ring
  | merge _ _ ih ih' => obtain ⟨P,hP⟩:=ih; obtain ⟨T,hT⟩:=ih'; refine ⟨P+T,fun t=>?_⟩; simp only [Pi.add_apply,hP t,hT t,Q,Polynomial.eval_add,mul_add]

private lemma drops {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x:E) (P:ℂ[X]) (n:ℕ) {G : ℂ→ℝ × E→ℂ} (hh:Wall (zone 1) (ticket (@id (ℝ × E))) 1 G)
    (h : ∀ t:ℝ, G 0 (Real.exp (-t),x)=(Real.exp (-t):ℂ)^n * Q P t): ∃ w:ℂ,P=C w:= by
  induction n generalizing G with
  | zero=>
    have hc : ContinuousAt (fun t:ℝ=>G 0 (t,x)) 0:= (hh.stream.smooth (0,(0:ℝ),x) ⟨zone_zero zero_lt_one,mem_univ _⟩).continuousAt.comp (x:=0)
      (f:=fun i:ℝ=>((0:ℂ),i,x)) (by fun_prop)
    have he := hc.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    simp_rw [Function.comp_def,h,pow_zero,one_mul] at he
    exact ⟨_,polynomial P he⟩
  | succ k ih=>
    have hl : ContinuousAt (fun t:ℝ=>G 0 (t,x)) 0:= (hh.stream.smooth (0,(0:ℝ),x) ⟨zone_zero zero_lt_one,mem_univ _⟩).continuousAt.comp (x:=0)
      (f:=fun i:ℝ=>((0:ℂ),i,x)) (by fun_prop)
    have ht := hl.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    have hz : G 0 (0,x)=0:= by
      apply tendsto_nhds_unique ht
      have hu:=(((Complex.continuous_ofReal.continuousAt (x:=0)).tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero).pow k).mul (damps P)
      simpa only [comp_def,h,pow_succ,mul_zero,mul_assoc] using hu
    apply ih (Ray.more Metric.isOpen_ball hh) _
    intro t; apply mul_left_cancel₀ (show (Real.exp (-t):ℂ)≠0 from by norm_cast; positivity)
    have hk:= Ray.splitAt hh (zone_zero zero_lt_one) (Real.exp (-t)) x
    rw [hz,zero_add,h] at hk; rw [← hk]; ring

theorem weights (h : Ledger A a F) (hs : ∀ r:ℝ, 0<r→F r=F 1) (n:ℕ)(x: External I n):
    (0 < a → F 1 n x=0) ∧ ∀ t:ℝ,0<t → F 1 n (move A t x)=(t:ℂ)^(-a)*F 1 n x:=by
  obtain ⟨P,hP⟩:= cone h x
  let g(t:ℝ):=F 1 n (move A t x)
  have hg (t : ℝ) : g (Real.exp (-t))=(Real.exp (-t):ℂ)^(-a)*Q P t:=by
    unfold g; rw [← hs (Real.exp t) (Real.exp_pos t)]
    rw [hP]; nth_rw 1 [Real.exp_neg]; simp
  have he : Canonical (F 1):= origin h 1
  have hk:= puts he.constant (B:=A) n (R:=1)
  let G (z:ℂ)(v : ℝ × External I n):=F 1 n (move A v.1 v.2)
  have hf : Wall (zone 1) (ticket (@id (ℝ × External I n))) 1 G:= hk
  have hplus (hp:0<a): P=0 := by
    have hc : ContinuousAt g 0:= (hf.stream.smooth (0,(0:ℝ),x) ⟨zone_zero zero_lt_one, mem_univ _⟩).continuousAt.comp (f:=fun i:ℝ=> ((0:ℂ),i,x)) (x:=0) (by fun_prop)
    have hv : Tendsto (fun t:ℝ=> (Real.exp (-t):ℂ)^a) atTop (nhds 0):= by
      lift a to ℕ using hp.le
      have ht:= ((Complex.continuous_ofReal.continuousAt (x:=0)|>.tendsto).comp Real.tendsto_exp_neg_atTop_nhds_zero).pow a
      simpa only [Complex.ofReal_zero,zero_pow (by exact_mod_cast hp.ne' : a≠0),comp_def,zpow_natCast] using ht
    apply Eq.trans (polynomial P (k:=0) ?_) (Polynomial.C_0)
    have ht:= hv.mul (hc.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero)
    rw [zero_mul] at ht; refine ht.congr (fun t=>?_); change (Real.exp (-t):ℂ)^a *g (Real.exp (-t))=_; rw [hg,zpow_neg,mul_inv_cancel_left₀]; exact zpow_ne_zero _ (by norm_cast; positivity)
  have h1 : g (Real.exp (-(0:ℝ)))= F 1 n x:=by simp [g,Momentum.one]
  constructor
  · intro hp; rw [← h1,hg,hplus hp]; simp [Q]
  obtain ⟨w,hw⟩: ∃ w:ℂ,P=C w:= by
    rcases lt_or_ge 0 a with hp|hp
    · exact ⟨0,(hplus hp).trans Polynomial.C_0.symm⟩
    have hx : (a.natAbs:ℤ)=-a:= by omega
    apply drops x P a.natAbs hf; intro t; change g _ = _; rw [hg,← hx,zpow_natCast]
  have hP : F 1 n x=w:=by rw [← h1,hg,hw]; simp [Q]
  intro t ht; change g t = _; rw [hP]; calc
    _ = g (Real.exp (- -Real.log t)) := by rw [neg_neg,Real.exp_log ht]
    _ = _ := by rw [hg,hw]; simp [Q,Real.exp_log ht]
end YM.MSbar.Pole.Spark
