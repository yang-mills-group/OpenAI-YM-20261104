import YM.Contacts.Pulse.Snug
/-! Finite conversion to the polynomial and temporal hierarchy. Includes the rank
zero constant on finite alphabets. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Filter Finset RG MvPolynomial
open scoped BigOperators Topology Classical NNReal
variable {α : Type*}[Fintype α]{n p q e a b:ℕ} (G:α→α→ℝ) {F H:ℕ→ Rack α}

def stage (e:ℕ)(F:Rack α) := ∑ r ∈ Finset.range (e+3),verse (F r)
variable (v:Plate α)
lemma cross_left (f:ℝ) : cross G (C f) v=0:= by simp [cross_apply]
lemma cross_right (f:ℝ): cross G v (C f)=0:= by simp [cross_apply]
lemma lap_const (f:ℝ):lap G (C f)=0:= by simp [lap_apply]
lemma lap_low (p:Field (Fin 1) α)(h:Poem p) : lap G (verse p)=0:= by simp_rw [lap_apply,verse_pderiv h,map_nsmul,verse_nil, MvPolynomial.pderiv_C]; simp

lemma hits_curve (h : Snug F) : lap G (stage e (F e))= ∑ r∈Finset.range (e+3),verse (Pulse.degree G (F e (r+2))):= by
  unfold stage; rw [map_sum,sum_range_succ',sum_range_succ' _ (e+1)]
  have hv (i:ℕ) (hi:e < i):Pulse.degree G (F e (i+2))=0:= by rw [h.thin _ _ (Or.inr (by omega)),nova]
  simp_rw [lap_low G _ (h.poems e (0+1)),show lap G (verse (F e 0))=0 from by rw [verse_nil,lap_const],add_zero]
  conv_rhs => rw [sum_range_succ _ (e+2),sum_range_succ _ (e+1)]
  rw [hv _ (by omega),hv _ (by omega),verse_quiet,verse_quiet,add_zero,add_zero]
  exact sum_congr rfl fun i _=> (lap_slot G (h.poems e (i+2))).symm
lemma light_curve (he:p+q=n)(h: Snug F)(hw:Snug H) : verse (light G n p q (F a) (H b))=cross G (verse (F a (p+1))) (verse (H b (q+1))) :=by subst n; rw [light,dif_pos rfl]; exact cross_slot G (h.poems _ _) (hw.poems _ _)

private lemma host (h : Snug F)(k:Snug H): ∑ i∈Finset.range (a+b+3), ∑ j∈ Finset.antidiagonal i, cross G (verse (F a (j.1+1))) (verse (H b (j.2+1))) = ∑ x∈ Finset.range (a+2),∑ y∈ Finset.range (b+2),cross G (verse (F a (x+1))) (verse (H b (y+1))):= by
  let X:=Finset.range (a+b+3); let T:= X.biUnion antidiagonal; let Y:= range (a+2) ×ˢ range (b+2)
  have he (p:ℕ×ℕ) : p∈T ↔ p.1+p.2<a+b+3:=by simp [T,X,mem_antidiagonal]
  rw [←sum_biUnion,←sum_product']; swap
  · intro i hi j hj hv; apply Finset.disjoint_left.mpr; intro p hp hz; exact hv ((mem_antidiagonal.mp hp).symm.trans (mem_antidiagonal.mp hz))
  symm; refine sum_subset (fun p hp=> (he p).mpr ?_) ?_
  · obtain ⟨h,w⟩:=mem_product.mp hp; rw [mem_range] at h w; omega
  intro i hi hn; simp only [mem_product,mem_range,not_and,not_lt] at hn
  by_cases he:i.1<a+2; · rw [k.thin b _ (Or.inr (by specialize hn he; omega)),verse_quiet,map_zero]
  rw [h.thin _ _ (Or.inr (by omega)),verse_quiet,map_zero,LinearMap.zero_apply]
lemma listPay_curve (he:a+b=e)(h:Snug F)(k:Snug H) : ∑ i ∈ range (e+3), verse (listPay G (F a) (H b) i)=cross G (stage a (F a)) (stage b (H b)):=by
  subst e; calc
    _ = ∑ i∈range (a+b+3),∑ j∈ antidiagonal i,cross G (verse (F a (j.1+1))) (verse (H b (j.2+1))) := sum_congr rfl fun i _=> by rw [listPay,verse_sum]; exact sum_congr rfl fun j hj=> light_curve G (mem_antidiagonal.mp hj) h k
    _ = _:= by
      rw [host G h k]; conv_rhs => unfold stage; rw [sum_range_succ',sum_range_succ' (fun i=> verse (H b i))];
      simp only [map_add,LinearMap.add_apply,map_sum,LinearMap.sum_apply]; rw [verse_nil,verse_nil,cross_left]; simp_rw [cross_left,cross_right]; simp; rw [sum_comm]
lemma wake_curve (h : Snug F): let Y:=gathering G F; stage e (wake G Y e n)= lap G (stage e (Y n e))+∑ p∈ Finset.antidiagonal e,∑ q∈Finset.antidiagonal n, cross G (stage p.1 (Y q.1 p.1)) (stage p.2 (Y q.2 p.2)):= by
  intro Y; conv_lhs => unfold stage; arg 2; intro r; unfold wake
  rw [show lap G (stage e (Y n e))=_ from hits_curve G (h.bounded G n)]; simp_rw [verse_add,verse_sum,sum_add_distrib]; congr 1; rw [sum_comm]; apply sum_congr rfl; intro i hi
  rw [sum_comm]; exact sum_congr rfl fun j _=> listPay_curve G (mem_antidiagonal.mp hi) (h.bounded G _) (h.bounded G _)
lemma staging (h:Snug F): let Y:=gathering G F; (n+1:ℕ) • stage e (Y (n+1) e)= lap G (stage e (Y n e))+∑ p∈ Finset.antidiagonal e,∑ q∈Finset.antidiagonal n, cross G (stage p.1 (Y q.1 p.1)) (stage p.2 (Y q.2 p.2)):= by
  intro Y; rw [← wake_curve G h]; simp only [Y,gathering_next,stage,verse_scale',← Finset.smul_sum,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; rw [mul_inv_cancel₀ (by exact_mod_cast n.succ_ne_zero),one_smul]
end YM.Pulse
