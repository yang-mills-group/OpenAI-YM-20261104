import YM.PertExtension.Reparameterize

/-!
# Coefficientwise (filtered) perturbative regulator limits under substitution

Formal convergence and positive-scale execution limits are distinct axes.
This is for the former, without summability in order. Continuity of ordinary
bare coefficients is not enough; the hypothesis used for the conversion to
the X variable needs ultraviolet convergence of already renormalized or
bounded auxiliary arrays in a common coupling first.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace YM.PertExtension.Position
open Set Function Filter PowerSeries Triangle
open scoped Topology BigOperators Classical
variable {α : Type*}

def AlignSeries (l : Filter α) (p : α→fps)(q : fps) := ∀ i, Tendsto (fun x=>coeff i (p x)) l (𝓝 (coeff i q))
namespace AlignSeries
variable {l : Filter α}{p q : α→fps}{a b : fps}
theorem const (a:fps):AlignSeries l (fun _=>a) a:=fun _=>tendsto_const_nhds
theorem add (h:AlignSeries l p a)(k:AlignSeries l q b):AlignSeries l (p+q) (a+b):=fun i=> by simpa using! (h i).add (k i)
theorem mul (h:AlignSeries l p a)(k:AlignSeries l q b):AlignSeries l (p*q) (a*b):=fun i=>by
   simp_rw [Pi.mul_apply,coeff_mul]
   exact tendsto_finsetSum _ fun j _=>(h j.1).mul (k j.2)
theorem pow (h:AlignSeries l p a)(k:ℕ) : AlignSeries l (p^k) (a^k):= by
   induction k with
   | zero=>simpa using! const (l:=l) 1
   | succ k ih=>simpa [pow_succ] using! ih.mul h
lemma scalar_C (p:α→ℝ)(x:ℝ)(h:Tendsto p l (𝓝 x)) : AlignSeries l (fun i=> C (p i)) (C x) := by
  intro i
  by_cases hi : i=0
  · subst i; simpa using h
  simpa only [coeff_C,if_neg hi] using! (tendsto_const_nhds (f:=l) (x:=(0:ℝ)))
theorem neg (h:AlignSeries l p a):AlignSeries l (-p) (-a):=fun i=>by simpa using! (h i).neg
theorem sub (h:AlignSeries l p a)(hh:AlignSeries l q b):AlignSeries l (p - q) (a - b):=h.add hh.neg
theorem sum {I}[Fintype I](f:α→I→fps)(g:I→fps)(hf:∀ i,AlignSeries l (fun v=>f v i) (g i)) : AlignSeries l (fun v=> ∑ i,f v i) (∑ i,g i) :=
  fun i=> by simp only [map_sum]; exact tendsto_finsetSum _ fun j _=> hf j i
theorem prod {I}(f:α→I→fps)(g:I→fps)(s:Finset I)(h:∀ i∈s,AlignSeries l (fun v=>f v i) (g i)):
    AlignSeries l (fun v=> ∏ i∈s,f v i) (∏ i∈s,g i) := by
   induction s using Finset.induction_on with
   | empty=>simpa using! const (l:=l) (1:fps)
   | insert i s hi ih=> simpa [hi] using! (h i (by simp)).mul (ih (fun j hj=>h j (by simp [hj])))

-- substitution is polynomial through every finite truncation.
theorem subst_finite {p:fps} (h : p.constantCoeff=0)(q:fps)(i:ℕ): coeff i (subst p q)= ∑ k∈Finset.range (i+1),coeff k q * coeff i (p^k) := by
  rw [PowerSeries.coeff_subst' (Triangle.good p h) _ i, finsum_eq_sum_of_support_subset _ (s:=Finset.range (i+1)) ?_]
  · simp only [smul_eq_mul]
  intro k hk; simp only [mem_support] at hk; simp; by_contra! ha
  apply hk
  rw [show coeff i (p^k)=0 from PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (b:=(k:ℕ∞)) (by exact_mod_cast ha) (le_order_pow_of_constantCoeff_eq_zero k h)), smul_zero]

theorem compose (hp: AlignSeries l p a)(hq:AlignSeries l q b)(h:a.constantCoeff=0)(h':∀ᶠ x in l, constantCoeff (p x)=0):
    AlignSeries l (fun x=>subst (p x) (q x)) (subst a b) := by
  intro i;rw [subst_finite h]
  exact (tendsto_finsetSum _ (fun k (_ : k∈Finset.range (i+1))=>
      (hq k).mul ((hp.pow k) i))).congr' (h'.mono fun v hv=> (subst_finite hv _ _).symm)

lemma inverse_est (hp:AlignSeries l p a)(ha:IsUnit (coeff 1 a)):
    AlignSeries l (fun i=>inverseScale (p i)) (inverseScale a):=by
   have hn := isUnit_iff_ne_zero.mp ha
   have htail : ∀ᶠ i in l,coeff 1 (p i) ≠ 0 := (hp 1).eventually (isOpen_compl_singleton.mem_nhds hn)
   let Q := fun n:ℕ=>∀ k≤n,Tendsto (fun i=> coeff k (inverseScale (p i))) l (𝓝 (coeff k (inverseScale a)))
   suffices ∀ n,Q n from fun n=>this n n (le_refl _)
   intro n; induction n with
   | zero=> intro i hi; interval_cases i
            simpa using! (tendsto_const_nhds (f:=l) (x:=(0:ℝ)))
   | succ n ih=>
     have he (x : fps)(hx:IsUnit (coeff 1 x)) :
        coeff (n+1) (inverseScale x) = if n=0 then (coeff 1 x)⁻¹ else -(coeff 1 x)⁻¹ * coeff (n+1) (PowerSeries.subst (∑ i:Fin (n+1), C (coeff i.val (inverseScale x)) * X^i.val) x) := by
       unfold inverseScale; simp_rw [dif_pos hx]
       letI := hx.invertible
       simp only [x.substInvOfIsUnit_eq_substInv hx, substInv, coeff_mk]
       split_ifs with h'
       · subst n; simp [PowerSeries.substInvFun, invOf_eq_inv]
       obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero h'
       simp [PowerSeries.substInvFun,invOf_eq_inv]
     intro k hk
     by_cases hy : k=n+1
     · subst k; by_cases hy':n=0
       · rw [he a ha,if_pos hy',hy']; exact ((hp 1).inv₀ hn).congr' (htail.mono fun i hi=> by simpa [hy'] using (he _ (isUnit_iff_ne_zero.mpr hi)).symm)
       let s (x:fps):=∑ i:Fin (n+1), C (coeff i.val (inverseScale x))*X^i.val
       have hz x : constantCoeff (s x)=0:=by simp only [s,map_sum,map_mul,map_pow,constantCoeff_X];refine Finset.sum_eq_zero fun i hi=>?_ ; by_cases h:i.val=0<;>simp [h]
       have hS:= AlignSeries.compose (p:=s ∘ p) (a:=s a) (AlignSeries.sum _ _ fun i=>
          ((scalar_C _ _ (ih i.val (by omega))).mul (const (l:=l) _))) hp (hz _) (Eventually.of_forall fun v=>hz _)
       have hv := ((hp 1).inv₀ hn).neg.mul (hS (n+1))
       have he' := (htail.mono fun i hi=>he (p i) (isUnit_iff_ne_zero.mpr hi))
       rw [he a ha, if_neg hy']
       exact hv.congr' (he'.mono fun i he=>by simpa only [Function.comp_apply,hy', if_false] using! he.symm)
     exact ih k (by omega)

variable {J P:Type*}{shape : P→ℕ}(T:Triangle shape J)
lemma calibrates {q : α→Mark J shape→fps}{Q : Mark J shape→fps}(h:coeff 1 (T.connected Q)≠0)
   (hq:∀ i,AlignSeries l (fun v=>q v i) (Q i)) :
   ∀ i,AlignSeries l (fun v=>T.remeasured (q v) i) (T.remeasured Q i) := by
    have he : AlignSeries l (fun i=> T.connected (q i)) (T.connected Q) := by
      exact ((hq _).sub (sum _ _ fun i=>(hq _).mul (hq _))).add ((const _).mul (prod _ _ _ fun i hi=>hq (T.one i)))
    have hb:AlignSeries l (fun i=> T.parameter (q i)) (T.parameter Q) :=
        (const _).mul (he.sub (scalar_C _ _ (by simpa using he 0)))
    exact fun i=>(inverse_est hb (T.linearTest Q |>.mpr h)).compose (hq i) (inverse_zero _) (Eventually.of_forall fun _=>inverse_zero _)

end AlignSeries
end YM.PertExtension.Position
