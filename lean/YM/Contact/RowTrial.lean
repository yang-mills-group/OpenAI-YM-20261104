import YM.Contact.Power

/-! Rows of a single joint smooth compact test at the first normal coordinate.
    The Taylor subtraction acts at fixed (unscaled) spectator coordinates. -/
set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory LinearMap ContinuousLinearMap
open scoped ContDiff BigOperators Topology
namespace YM.Contacts
namespace Patch
variable {A B:Type*}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup B][NormedSpace ℝ B]

abbrev pin (B:Type*) [NormedAddCommGroup B][NormedSpace ℝ B]: A→L[ℝ] (A×B):=(ContinuousLinearMap.id ℝ A).prod (0:A→L[ℝ] B)

def slice (φ:Trial (A×B))(y:B): Trial A:=⟨fun x=>φ (x,y),φ.contDiff.comp (contDiff_id.prodMk contDiff_const), by
     refine (φ.hasCompactSupport.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) ?_
     intro x hx; have hx':= tsupport_comp_subset_preimage (φ:A×B→ℂ) (continuous_id.prodMk continuous_const) hx
     exact ⟨(x,y),hx',rfl⟩,fun _ _=>trivial⟩

lemma slice_iter (φ:Trial (A×B))(y:B)(n:ℕ)(x:A):
     iteratedFDeriv ℝ n (slice φ y) x = (iteratedFDeriv ℝ n φ (x,y)).compContinuousLinearMap (fun _=>pin B):=by
      let q(p:A×B):=φ (((0, y):A×B)+p)
      have he : (fun j=>slice φ y j)=q∘pin B:=funext fun i=>(congr_arg φ (by simp [pin])).symm
      have hg:ContDiff ℝ (↑n:ℕ∞ω) q:= (φ.orders _).comp (contDiff_const.add contDiff_id)
      rw [show ⇑(slice φ y)=q∘pin B from he,(pin B).iteratedFDeriv_comp_right hg _ (le_refl _)]
      congr 1; dsimp only [q]; simp [iteratedFDeriv_comp_add_left,pin]

lemma slice_major {φ:Trial (A×B)}(y:B){n:ℕ}{r:ℝ}(h:Major n φ r) : Major n (slice φ y) r :=by
     have hh(v:A): ‖pin B v‖=‖v‖:=by simp [pin,Prod.norm_def]
     intro i hi x;rw [slice_iter];refine ContinuousMultilinearMap.opNorm_le_bound h.nonneg fun m=>?_ ; exact ((iteratedFDeriv ℝ i φ (x,y)).le_opNorm _).trans (by change ‖(iteratedFDeriv ℝ i φ (x,y))‖ * (∏ i, ‖pin B (m i)‖) ≤ _; simp_rw [hh];exact mul_le_mul_of_nonneg_right (h i hi _) (Finset.prod_nonneg fun _ _=>norm_nonneg _))

/-- Keep only test derivatives *in the normal argument*. -/
def row (s:ℝ)(m:ℤ)(φ:Trial (A×B))(z:A×B):ℂ:= remainder s m (slice φ z.2) z.1
lemma uncut {s:ℝ}{m:ℤ}(hm:m<0)(φ:Trial (A×B)):row s m φ=φ:=funext fun z=>(by unfold row remainder taylorCut; rw [if_neg (not_le.mpr hm),sub_zero];rfl)
lemma row_add (s:ℝ)(m:ℤ)(φ ψ:Trial (A×B)):row s m (φ+ψ)=row s m φ+row s m ψ:= funext fun z=>by unfold row; rw [show slice (φ+ψ) z.2=slice φ z.2+ slice ψ z.2 from TestFunction.ext fun _=>rfl,rem_add];rfl
lemma row_smul (s:ℝ)(m:ℤ)(r:ℂ)(φ:Trial (A×B)):row s m (r • φ) = r • row s m φ:= funext fun z=>by unfold row; rw [show slice (r • φ) z.2=r • slice φ z.2 from TestFunction.ext fun _=>rfl,rem_smul];rfl

lemma row_cont (s:ℝ)(m:ℤ)(φ:Trial (A×B)):Continuous (row s m φ):=by
       suffices hg:Continuous (fun z:A×B=>taylorCut s m (slice φ z.2) z.1) from φ.continuous.sub hg
       unfold taylorCut; split_ifs
       · apply Continuous.smul ((lamp.continuous).comp ((continuous_norm.comp ((continuous_const_smul s⁻¹).comp continuous_fst)).pow 2))
         unfold polynomial; refine continuous_finsetSum _ fun i _=> ?_
         unfold jet; simp_rw [slice_iter]; refine Continuous.const_smul (c:=((i.factorial:ℝ)⁻¹)) (g:=fun z:A×B=>(iteratedFDeriv ℝ i φ (0,z.2)).compContinuousLinearMap (fun _=>pin B) (fun _=>z.1 - 0)) ?_
         have hc:= (φ.orders i).continuous_iteratedFDeriv (m:=i) le_rfl
         refine (continuous_eval (F:= _ [×i]→L[ℝ] ℂ)).comp ((hc.comp (continuous_const.prodMk continuous_snd)).prodMk ?_)
         exact continuous_pi (fun _=>(pin B).continuous.comp (continuous_fst.sub continuous_const))
       exact continuous_const

lemma slice_support {K:Set (A×B)} (φ:Trial (A×B))(y:B)(hp:y∉Prod.snd '' K)(h:Function.support ⇑φ ⊆ K): slice φ y=0 := TestFunction.ext (fun x=>notMem_support.mp fun hx=>hp ⟨(x,y),h hx,rfl⟩)
lemma zero_out {K:Set (A×B)}(s:ℝ)(m:ℤ)(φ:Trial (A×B))(h:Function.support ⇑φ ⊆ K)(x:A)(y:B)(hp:y∉Prod.snd '' K): row s m φ (x,y)=0 := by
       rw [row,slice_support _ _ hp h]; change remainder _ _ (0:A→ℂ) _ = _; simp [remainder,taylorCut,polynomial,jet]

variable [FiniteDimensional ℝ A]
lemma compact_row {K:Set (A×B)}{W:Set (A×B)} {s:ℝ}(hs:0<s) {m:ℤ}(hK:IsCompact K)(hh:K ⊆ W)(hm:0 ≤ m → Set.univ (α:=A) ×ˢ ((Prod.snd) '' K) ⊆ W) : ∃ L, IsCompact L ∧ L ⊆ W∧∀ φ:Trial (A×B),tsupport ⇑φ ⊆ K → Function.support (row s m φ) ⊆ L :=by
       by_cases hx : m<0
       · exact ⟨K,hK,hh,fun φ h=> (uncut hx φ).symm ▸ subset_closure.trans h⟩
       refine ⟨K ∪ (Metric.closedBall 0 (2*s) ×ˢ (Prod.snd '' K)), hK.union ((isCompact_closedBall ..).prod (hK.image continuous_snd)),Set.union_subset hh ((Set.prod_mono_left (Set.subset_univ _)).trans (hm (not_lt.mp hx))),fun φ h z hz=> ?_⟩
       by_contra! h'
       have hr:z.1 ∈ Metric.closedBall 0 (2*s) → z.2∉ (Prod.snd '' K):= fun h1 h2=> h' (Or.inr ⟨h1,h2⟩)
       by_cases hk : z.1∈Metric.closedBall 0 (2*s)
       · exact hz (zero_out _ _ _ (subset_closure.trans h) _ _ (hr hk))
       rw [mem_closedBall_zero_iff] at hk
       apply hz; unfold row remainder taylorCut;rw [if_pos (not_lt.mp hx),chi_lt_zero s hs z.1 (not_le.mp hk),zero_smul,sub_zero]; exact notMem_support.mp fun hw=> h' (Or.inl (h (subset_closure hw)))

omit [FiniteDimensional ℝ A] in
lemma row_sep {s:ℝ}{m:ℤ} (φ:Trial (A×B))(h: tsupport φ ⊆ {p:A×B|p.1≠0}): row s m φ=φ:=by
     funext z; unfold row remainder taylorCut; split_ifs
     · rw [polynomial,Finset.sum_eq_zero (fun i _=> ?_),smul_zero,sub_zero]; rfl
       have hz: (0:A)∉tsupport (slice φ z.2):=fun he=> (h (tsupport_comp_subset_preimage (φ:A×B→ℂ) (continuous_id.prodMk continuous_const) he)) rfl
       unfold jet; simp [Function.notMem_support.mp (show 0∉Function.support (iteratedFDeriv ℝ i (⇑(slice φ z.2))) from fun h' => hz (support_iteratedFDeriv_subset _ h'))]
     rw [sub_zero];rfl

end Patch
end YM.Contacts
