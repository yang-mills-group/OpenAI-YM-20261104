import YM.WilsonCoeffUV.Thermo.Distance
/-!
# Separable tariff functions. True and periodic. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B σ η : ℝ}

lemma cap_nn {f:ι→ℝ}(h:SumBudget f A): 0≤A:= (tsum_nonneg h.1).trans h.2.2
lemma cap_pt {f:ι→ℝ}(h:SumBudget f A)(i:ι): f i ≤ A:= (h.2.1.le_tsum _ (fun _ _=> h.1 _)).trans h.2.2
lemma prod_cap {f:U→ℝ} {g:U→ι→ℝ} (h:SumBudget f A)(hp:0≤B)(e:∀ u,SumBudget (g u) B): SumBudget (fun i:U×ι=>f i.1*g i.1 i.2) (A*B):=by
  have he u: Summable fun i=> f u*g u i:= (e u).2.1.mul_left _
  let t (i:U×ι):= f i.1 * g i.1 i.2
  have ht (i:U×ι):0 ≤ t i := mul_nonneg (h.1 _) ((e _).1 _)
  have hw (u:U) : ∑' i,t (u,i)≤f u*B:= by simp only [t]; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (e u).2.2 (h.1 _)
  have hb:= h.2.1.mul_right B
  have hv : Summable (fun u=>∑' i,t (u,i)):= hb.of_nonneg_of_le (fun i=>tsum_nonneg fun j=> ht (i,j)) hw
  have hh :=(summable_prod_of_nonneg ht).mpr ⟨he,hv⟩
  refine ⟨ht,hh,?_⟩
  change (∑' i,t i)≤_
  rw [hh.tsum_prod]; exact (hv.tsum_le_tsum hw hb).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hp)

lemma cap_walk (f:U→ℝ)(g:ι→ℝ) (q: ι ≃ U)(h:∀ i, f (q i)=g i) (he:SumBudget g A):SumBudget f A:=by
  have hh: g=f ∘ q:= funext fun i=> (h i).symm
  subst g; refine ⟨fun i=>?_, q.summable_iff.mp he.2.1,?_⟩
  · simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he.1 (q.symm i)
  rw [← q.tsum_eq f]; exact he.2.2
lemma cap_scale {f: U→ℝ}(h:SumBudget f A) {c:ℝ}(hp:0≤c): SumBudget (fun i=> c*f i) (c*A):=⟨fun _=>mul_nonneg hp (h.1 _),h.2.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hp⟩
lemma series_bill {f:U→ℝ}(h:SumBudget f A)(r:ℕ) : SumBudget (fun m:Fin r→U=>∏ i,f (m i)) (A^r):=by
  induction r with
  | zero=>
    have he (p : Fin 0→U): (∏ i:Fin 0,f (p i))=1 := by simp
    simp_rw [he,pow_zero]; exact ⟨fun _=>zero_le_one,summable_of_hasFiniteSupport (Set.toFinite _) ,by rw [tsum_fintype]; simp⟩
  | succ r ih=> exact cap_walk _ _ (Fin.consEquiv (fun _:Fin (r+1)=> U)) (fun i=> by rw [Fin.prod_univ_succ]) (by rw [pow_succ']; exact prod_cap h (pow_nonneg (cap_nn h) _) (fun _=>ih))

lemma series_way [Fintype U](f:U→ℝ)(r:ℕ):∑ m:Fin r→U, (∏ i, f (m i)) = (∑ u,f u)^r := by rw [← Fintype.prod_sum (fun _ i=> _)]; simp

section
variable [Fintype α]
def keys (p:Cover)(η:ℝ) (i:Cloth α):=Real.exp (-η*terrain.gap p i.1)
def boardPay (α:Type*) [Fintype α] (σ:ℝ):= sheetPay σ * Fintype.card α
lemma boardPay_nn {σ:ℝ}(h:0<σ):0≤ boardPay α σ:= mul_nonneg (sheetPay_pos _ h).le (by positivity)
lemma keys_cost (p:Cover)(h:0<η): SumBudget (keys (α:=α) p η) (boardPay α η):=by
  have he : SumBudget (fun i:Cover=>Real.exp (-η*terrain.gap p i)) (sheetPay η):= cap_walk _ _ (Equiv.addLeft p) (fun i=> by change Real.exp (-η*size (p+i-p))= _; rw [add_sub_cancel_left]) (Width.compactPay _ h)
  have hv : SumBudget (fun _ : α=> (1:ℝ)) (Fintype.card α):= ⟨fun _=> by positivity,summable_of_hasFiniteSupport (Set.toFinite _) ,by simp⟩
  change SumBudget (fun i:Cover×α=>Real.exp _) (sheetPay η * Fintype.card α); simpa only [mul_one] using prod_cap he (by positivity) (fun _=>hv)

lemma keys_native (p: Site n)(h:0<η): ∑ i: Co n α,Real.exp (-η*(tor n).gap p i.1) ≤ boardPay α η:= by
  have he : ∑ i:Site n,Real.exp (-η*(tor n).gap p i) ≤sheetPay η:= taxi_volume p η h
  rw [Fintype.sum_prod_type, Finset.sum_comm]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; unfold boardPay; rw [mul_comm]; exact mul_le_mul_of_nonneg_right he (by positivity)
end
-- plan functions
abbrev sail {U α:Type*} [Fintype ι](σ:ℝ)(d:Distance U)(p:U)(m:ι→U×α): ℝ:= ∏ i,Real.exp (-σ*d.gap p (m i).1)
variable {d:Distance U}
lemma sail_nn [Fintype ι](p:U)(m:ι→U×α): 0≤sail σ d p m:= Finset.prod_nonneg fun _ _=>by positivity
lemma train_pay [Fintype α] (h:0<η)(p:Cover)(k:ℕ) : SumBudget (fun i:Fin k→Cloth α=>sail η terrain p i) ((boardPay α η)^k):= series_bill (keys_cost p h) k
lemma train_native [Fintype α] (h:0<η)(p:Site n)(k:ℕ) : ∑ i:Fin k→ Co n α,sail η (tor n) p i≤(boardPay α η)^k:= by
  unfold sail; rw [series_way (U:=Co n α) (fun i=> Real.exp (-η*(tor n).gap p i.1))]; exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _=> by positivity) (keys_native p h) _
lemma sail_cut {v l:ℕ}(hv:v≤l)(hη:0≤η)(he:η<σ)(hk:0<k) (p:U)(m:Fin k→ U×α)(hh:∀ i,d.gap p (m i).1 ≤ l): Real.exp (-σ*l) ≤ Real.exp (-η*v) * sail ((σ-η)/k) d p m:=by
  let c := (σ-η)/k; have ht:0≤c:= div_nonneg (sub_nonneg.mpr he.le) (by positivity)
  have h : ∏ _ : Fin k,Real.exp (-c*l) ≤ sail c d p m:= Finset.prod_le_prod (fun _ _=>by positivity) (fun i _=>Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (hh i)) (neg_nonpos.mpr ht)))
  have hc : (k:ℝ)*(-c*l)= (η-σ)*l:=by
    have h': (k:ℝ)≠0:= by positivity
    unfold c; field_simp; ring
  simp_rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul,hc] at h
  apply le_trans _ (mul_le_mul_of_nonneg_left h (by positivity : 0≤Real.exp (-η*v)))
  rw [← Real.exp_add, Real.exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_left (show (v:ℝ)≤l from Nat.cast_le.mpr hv) hη]
end YM.WilsonCoeffUV.Bank
