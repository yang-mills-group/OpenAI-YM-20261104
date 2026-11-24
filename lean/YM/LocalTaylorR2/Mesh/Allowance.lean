import YM.LocalTaylorR2.Mesh.Parcels
/-! # Budget recurrence on the augmented last slot, all powers without pointwise divisors in microscopic comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open ConnectedActivityE6.Blaze Finset Filter Topology
open scoped BigOperators Classical ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E} {u d c r θ θ' :ℝ} {j m n l:ℕ} {f g:E→ ℝ}

def absorb (i:Series.Letter m)(x y:ℝ):= if i=Fin.last _ then Series.split i x+(∑ i: Fin m, (Series.mono (i.val+1) x-Series.mono (i.val+1) y)) else Series.split i y
lemma absorb_last (x y:ℝ) (m:ℕ) : (∑ i:Series.Letter m, absorb i x y)= ∑ i:Series.Letter m, Series.split i x:=by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp [absorb,Series.split, Series.rank,Finset.sum_sub_distrib]
  ring

private lemma harmPow (hr:0≤c) (_hd:0≤d) (hh : Brush j 1 d f x)(hk:Brush j 2 d g x)(hp:Brush j c d (fun x=>f x-g x) x)(n:ℕ): Brush j ((4:ℝ)^n*c) (d*n) (fun x=> f x^n-g x^n) x:= by
  induction n with
  | zero => exact Brush.zi (Eventually.of_forall fun _=>by simp) (by positivity) (by simp)
  | succ n ih=>
    have he: (fun x=>f x^(n+1)-g x^(n+1))=fun x=> f x^n*(f x-g x)+(f x^n-g x^n)*g x:=by ext; ring
    have HT:= ((Series.power hh n).paints hp).gathering (ih.paints hk)
    rw [he]; refine HT.climb ?_ (le_of_eq (by push_cast; ring))
    rw [one_pow,one_mul,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=n) (show (1:ℝ)≤4 by norm_num)) hr]
lemma monoharm (hr:0≤c) (hd:0≤d) (hh : Brush j 1 d f x)(hk:Brush j 2 d g x)(hp:Brush j c d (fun x=>f x-g x) x)(n:ℕ) : Brush j ((4:ℝ)^n*c) (d*n) (fun x=>Series.mono n (f x)-Series.mono n (g x)) x:=by
  let u := ((n.factorial:ℝ)⁻¹); have hu : ‖u‖≤1 :=by
    have hy : (1:ℝ)≤(n.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos n
    unfold u; rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hy
  rw [show (fun x=>Series.mono n (f x)-Series.mono n (g x))=fun x=> u • (f x^n-g x^n) by ext; simp only [u,Series.mono,smul_eq_mul]; ring]
  exact ((harmPow hr hd hh hk hp n).smul u).climb (mul_le_of_le_one_left (by positivity) hu) le_rfl
lemma budgetPow (_p:0≤r)(_hr:r≤1)(hp:0≤u)(he:u≤r) : u^(n+1) ≤ u*r^n:= by
 rw [pow_succ,mul_comm u]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp he n) hp
lemma allows_growth (hc: θ≤θ') (h:Charge.Allows m j θ): Charge.Allows m j θ' := by
  intro i E _ _ f x v d hh hx; exact (h i E f x v d hh hx).climb (mul_le_mul_of_nonneg_right hc (pow_nonneg hh.nonneg _)) le_rfl

def Carry (m j:ℕ) (θ:ℝ):Prop := Charge.Allows m j θ ∧ ∀ (i:Series.Letter m) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f g:E→ℝ) (x:E) (v d r:ℝ), Brush j v d f x → Brush j (v*r^m) d (fun x=>f x-g x) x→ 0≤r → r≤1 → v≤r → Brush j (θ*(v*r^i.val)) (d*(m+3:ℝ)) (fun x=> absorb i (f x) (g x)) x
lemma carries (m j:ℕ) : ∃ θ:ℝ, 1≤ θ ∧ Carry m j θ:= by
  obtain ⟨C,hC,h⟩:= Series.allowance m j
  let b :ℝ := m*4^m
  have hb:b≥0:=by unfold b; positivity
  let D:ℝ:= C+b; have hD:C≤ D:=le_add_of_nonneg_right hb
  let U:ℝ:=4^(m+1); have hU:1≤U:=one_le_pow₀ (by norm_num)
  refine ⟨D+U,(hC.trans hD).trans (le_add_of_nonneg_right (zero_le_one.trans hU)), allows_growth (hD.trans (le_add_of_nonneg_right (zero_le_one.trans hU))) h,?_⟩
  intro i E _ _ f g x v d r hp hf hr hr' hh
  have he:= hp.nonneg; have hy := hp.pos
  have ht: Brush j (2*v) d g x:= by
    refine ((hp.separating hf).shimmy (Eventually.of_forall fun x=> Eq.symm (sub_sub_cancel (f x) (g x)))).climb ?_ le_rfl
    have h: r^m≤1:= pow_le_one₀ hr hr'
    linarith only [mul_le_mul_of_nonneg_left h he]
  unfold absorb; split_ifs with hb'; swap
  · unfold Series.split; have hk : i.val< m:= lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (fun h=> hb' (Fin.ext h))
    simp_rw [if_pos hk]
    let t:= ((Series.rank i).factorial:ℝ)⁻¹
    have hu : ‖t‖≤1:=by
      have hz : (1:ℝ)≤((Series.rank i).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (Series.rank i)
      unfold t; rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hz
    rw [show (fun x=>Series.mono (Series.rank i) (g x))=fun x=> t • (g x^Series.rank i) by ext; simp only [t,Series.mono,smul_eq_mul]; ring]
    refine ((Series.power ht (Series.rank i)).smul t).climb ((mul_le_of_le_one_left ?_ hu).trans ?_) (mul_le_mul_of_nonneg_left ?_ hy)
    · positivity
    · have he:= budgetPow hr hr' he hh (n:=i.val)
      have hv : (2:ℝ)^Series.rank i ≤ D+U:=by
        apply le_trans (b:=U); swap; exact le_add_of_nonneg_left (zero_le_one.trans (hC.trans hD))
        exact (pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) (by norm_num) _).trans (pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hk.le))
      have hw:0≤v:= hp.nonneg; rw [mul_pow]; exact mul_le_mul hv he (pow_nonneg hw _) (by linarith)
    unfold Series.rank; push_cast; have hpi : (i.val:ℝ)< m:=by exact_mod_cast hk
    linarith
  subst i
  have hx:= h (Fin.last m) E f x v d hp (hh.trans hr')
  have hw:v*r^m≥0:= by positivity
  let k:ℝ:=4^m*(v*r^m); let p :ℝ := d*(m+3:ℝ)
  have he' (i:Fin m): Brush j k p (fun x=>Series.mono (i.val+1) (f x)-Series.mono (i.val+1) (g x)) x:= by
    apply (monoharm hw hy (hp.climb (hh.trans hr') le_rfl) (ht.climb ?_ le_rfl) hf (i.val+1)).climb (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) i.isLt) hw) (mul_le_mul_of_nonneg_left ?_ hy)
    · linarith
    push_cast; have hx : (i.val:ℝ)< m:=by exact_mod_cast i.isLt
    linarith
  apply (hx.gathering (Brush.spree univ (fun i:Fin m=>fun x=>Series.mono (i.val+1) (f x)-Series.mono (i.val+1) (g x)) (fun _=>k) hx.pos (fun i _=>he' i))).climb _ le_rfl
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin, Fin.val_last]
  rw [show ↑m*k=b*(v*r^m) by unfold k b; ring]
  refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left (budgetPow hr hr' he hh) (zero_le_one.trans hC)) _) ?_
  rw [Fin.val_last]; unfold D; nlinarith
end YM.LocalTaylorR2.Mesh
