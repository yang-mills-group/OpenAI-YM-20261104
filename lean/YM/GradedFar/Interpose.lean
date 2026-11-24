import YM.GradedFar.Layaway
/-!
# Prices following all substitutions of frame steps
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Cart
open Function Filter Set PowerSeries
open MS.Book.Program MS.Book.Convolve
open scoped Topology BigOperators Classical
variable {I : Type*} {L : I → ℝ} {J : Type*} {z : I → ℂ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {f f' : I → E} {g : I → F}

def Beyond (p:ℕ) (z:I→ℂ)(L:I→ℝ)(f:I→E) := ∃ u:I→E, Charge L u ∧ ∀ i, f i=z i^p • u i
variable {p:ℕ} {A:E→ₗ[ℂ] F→ₗ[ℂ] G}
lemma Beyond.bound (h:Beyond p z L f): ∀ᶠ k:ℕ in atTop,∀ᶠ C:ℝ in atTop, ∀ i,
    ‖f i‖ ≤ C*(1+|L i|)^k*‖z i‖^p:= by
 obtain ⟨u,hU,h⟩:=h; filter_upwards [poly.upgrade hU] with k hk
 filter_upwards [poly.limit hk] with C hC i; rw [h i,norm_smul,norm_pow,mul_comm]; exact
   mul_le_mul_of_nonneg_right (hC i) (by positivity)
lemma Beyond.add (h:Beyond p z L f)(hv:Beyond p z L f') : Beyond p z L (fun i=> f i+f' i):=by
 obtain ⟨u,he,h⟩:= h; obtain ⟨v,hh,hv⟩:= hv; exact ⟨_, he.add hh,fun i=> by dsimp only; rw [h i,hv i,smul_add]⟩
lemma Beyond.sum (s:Finset J){u:J→I→E}(h:∀ i∈s,Beyond p z L (u i)): Beyond p z L (fun i=>∑ j∈s,u j i):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact ⟨_,Charge.const 0,fun i=>(smul_zero (z i^p)).symm⟩
 | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h _ (Finset.mem_insert_of_mem hj))
lemma Beyond.pair_left (ha:Hands A)(h:Beyond p z L f)(hv:Charge L g): Beyond p z L (fun i=> A (f i) (g i)):=by
 obtain ⟨u,he,h⟩:= h; exact ⟨_,ha.charge he hv,fun i=>by dsimp only; rw [h i,map_smul,LinearMap.smul_apply]⟩
lemma Beyond.pair_right (ha:Hands A)(h:Charge L f)(hv:Beyond p z L g): Beyond p z L (fun i=> A (f i) (g i)):=by
 obtain ⟨u,he,hv⟩:= hv; exact ⟨_,ha.charge h he,fun i=>by dsimp only; rw [hv i,map_smul]⟩
abbrev budget {f:I→ℕ→E} (u:I→ℝ) := ∀ n:ℕ,Charge u (fun i=> f i n)
-- consuming interface uses `Feasible`, not an existence statement for CPS substitutions.
abbrev Feasible (f:I→ℕ→E)(u:I→ℝ) := budget (f:=f) u
lemma together_sub {f:I→ℕ→E}{c:I→Cn}(h:Feasible f L) (ht:∀ n:ℕ,Feasible (fun i k=>coeff k (c i ^ n)) L):
    Feasible (fun i=>substitute (c i) (f i)) L:=by
 intro n; simp_rw [rules]; exact Charge.sum _ (fun i _=> Charge.smul (ht i n) (h i))
lemma total_crop (p:ℕ){f:I→ℕ→E} (hz:Charge L z)(hf:Feasible f L):Charge L (fun i=> operation p (z i) (f i)):=
  Charge.sum _ (fun k _=> (hz.pow k).smul (hf k))
lemma omitted_pair {f:I→ℕ→E}{g:I→ℕ→F}(ha:Hands A)(p:ℕ)(h:Feasible f L) (hv:Feasible g L)(hz:Charge L z):
    Beyond (p+1) z L (fun i=> A (operation p (z i) (f i)) (operation p (z i) (g i)) - operation p (z i) (pairW A (f i) (g i))):=by
 simp_rw [pair]; exact ⟨fun i=> outsidePay p (z i) A (f i) (g i), Charge.sum _ (fun x _=>
   (hz.pow _).smul (ha.charge (h x.1) (hv x.2))),fun i=>rfl⟩
lemma hands_scalar : Hands (LinearMap.mul ℂ ℂ):= ⟨1,zero_le_one,fun _ _=>by rw [one_mul]; exact (norm_mul ..).le⟩
lemma omitted_pow (p:ℕ){c:I→Cn}(h:∀ n:ℕ,Feasible (fun i k=> coeff k (c i ^n)) L)(hz:Charge L z)(j:ℕ):
    Beyond (p+1) z L (fun i=> (operation p (z i) (ofPS (c i)))^j-operation p (z i) (ofPS (c i^j))):= by
 have hf:Feasible (fun i=>ofPS (c i)) L := by
    intro n; specialize h 1 n; simp_rw [pow_one] at h; exact h
 induction j with
 | zero=>simp only [pow_zero]
         have he i : operation p (z i) (ofPS 1) = (1:ℂ) := by
            rw [operation,Finset.sum_eq_single 0]
            · simp [ofPS]
            · exact fun j _ hj=>by rw [ofPS,coeff_one,if_neg hj,smul_zero]
            simp
         simp_rw [he,sub_self]; exact ⟨_,Charge.const 0,fun i=>(smul_zero (z i^(p+1))).symm⟩
 | succ j ih =>
    have hx:= omitted_pair hands_scalar p (h j) hf hz; have hv:= Beyond.pair_left hands_scalar ih (total_crop p hz hf); obtain hv:= hv.add hx; refine Eq.mp ?_ hv; congr! 1; ext1 i
    let f:= ofPS (c i^j)
    -- coefficients payment, order orientation
    have hd (k): pairW (LinearMap.mul ℂ ℂ) f (ofPS (c i)) k= ofPS (c i ^(j+1)) k:= by
      rw [ofPS, pow_succ, coeff_mul]; rfl
    simp_rw [LinearMap.mul_apply']; -- prove using hd
    change _ + (_ -operation p (z i) (pairW _ f _))= _
    rw [funext hd, pow_succ]; ring
lemma omitted_interpose {f:I→ℕ→E} {c:I→Cn}(p:ℕ)(h:Feasible f L)(hc:∀ n,Feasible (fun i k=>coeff k (c i^n)) L)
    (hroot:∀ i,Rooted (c i))(hz:Charge L z):
    Beyond (p+1) z L (fun i=> operation p (operation p (z i) (ofPS (c i))) (f i) - operation p (z i) (substitute (c i) (f i))):=by
 simp_rw [apply_through _ _ _ (hroot _)]; change Beyond _ _ _ (fun i=> (∑ j∈Finset.range (p+1), _ • f i j) - _)
 simp_rw [← Finset.sum_sub_distrib, ← sub_smul]; refine Beyond.sum _ fun i _=>?_ ; obtain ⟨u,hu,hx⟩:= omitted_pow p hc hz i
 refine ⟨_,hu.smul (h i),fun j=>?_⟩; dsimp only at hx ⊢; rw [hx j,smul_eq_mul,smul_smul]
lemma crop_suffix {f:I→ℕ→E}(p k:ℕ)(hkp:k≤ p+1)(h:Feasible f L)(hz:Charge L z):
    Beyond k z L (fun i=> operation p (z i) (f i)-∑ j∈Finset.range k,z i^j • f i j):=by
 unfold operation; simp_rw [← Finset.sum_Ico_eq_sub _ hkp]; refine Beyond.sum _ (fun i hi=>?_ )
 exact ⟨_, (hz.pow (i-k)).smul (h i), fun j=> by rw [smul_smul, ← pow_add, Nat.add_sub_of_le (Finset.mem_Ico.mp hi).1]⟩
end YM.FVA2.GradedFar.Cart
