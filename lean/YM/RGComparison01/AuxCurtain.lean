import YM.RGComparison01.AuxJets
import YM.Extra.WILSON_STARTUP.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Blips

/-! # Real rescaled tests, simple product calculus with remainder

 Keep value factors in true units. Taylor tail by vanishing in the same norm as
 the jets (no analytic disks assumed). -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxCurtain
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp  Work.G05
open AuxJets PhysicalNext.Repeat WilsonStartup Tensor
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {p v u d e s a C : ℝ} {j k n m : ℕ} {x : E} {f g : E→ℝ}

lemma product_flat (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hp : FlatAt k f x) (hh : FlatAt j g x) (h : m < k+j) (hi : m ≤ n) :
    iteratedFDeriv ℝ m (fun i=>f i*g i) x=0:= by
  have hm : (m:WithTop ℕ∞) ≤ (n:WithTop ℕ∞):=Nat.cast_le.mpr hi
  let B:= ContinuousLinearMap.mul ℝ ℝ; let u y:= f y*g y
  apply norm_le_zero_iff.mp
  obtain ⟨l,hl,hx,Hl⟩:= hf.contDiffOn' le_rfl (by simp)
  obtain ⟨l',hl',hx',HL⟩:= hg.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at Hl HL
  let s:= l∩l'; have he : IsOpen s:= hl.inter hl'
  have hz : x∈s:=⟨hx,hx'⟩
  rw [← iteratedFDerivWithin_of_isOpen m he hz]
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear (Hl.mono (Set.inter_subset_left))
    (HL.mono (Set.inter_subset_right)) he.uniqueDiffOn hz hm).trans ?_
  rw [Finset.sum_eq_zero]; swap
  · intro i hi; rw [Finset.mem_range] at hi
    rcases lt_or_ge i k with h|h
    · rw [iteratedFDerivWithin_of_isOpen i he hz,hp _ h]; simp
    rw [iteratedFDerivWithin_of_isOpen (m-i) he hz,hh _ (by omega)]; simp
  rw [mul_zero]

lemma prod_fades (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hp : FlatAt k f x) (hh : FlatAt j g x) (hi : k+j ≤ n+1) : FlatAt (k+j) (fun i=>f i*g i) x:= fun m h=> product_flat hf hg hp hh h (by omega)
lemma pow_fades (hf : ContDiffAt ℝ n f x) (hp : FlatAt k f x)
    (hi : k*j ≤ n+1) : FlatAt (k*j) (fun i=> f i^j) x:= by
  induction j with
  | zero=> rw [mul_zero]; exact fun i hi=>False.elim (by omega)
  | succ j ih=> simp only [pow_succ,Nat.mul_succ] at hi ⊢; exact prod_fades (hf.pow _) hf (ih (by omega)) hp hi

lemma vanishing {f:E→F} (h : ∀ x ∈ ball 0 a, Brush n C 1 f x) (hv : FlatAt k f 0)
    (hp : 0 < a) (ht : a ≤ 1) (hk : k ≤ n) (hx : x∈ball 0 a) : Brush n (C*a^k) a⁻¹ f x:= by
  have he := Shellac.pools hp ht hk (h _ hx).nonneg (le_refl 0) (fun i hi=>(h i hi).smooth) (fun i _ hi x hx => (Brush.offer.1 (h x hx)).2 i hi) (fun i hi=>by unfold normJ; rw [hv i hi, norm_zero,zero_mul]) x hx; simpa using he

lemma diagonal_high {f : E→F} (h : ContDiffAt ℝ (↑k) f 0) {i : ℕ} (hi : k < i) (x : E) :
    iteratedFDeriv ℝ i (diagonal (coeff f k 0)) x=0:= by
  cases k with
  | zero => rw [show diagonal (coeff f 0 0)=(fun x=> f 0) from funext fun _=> Tensor.coeff_apply_zero f 0 _]; obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi.ne'; rw [iteratedFDeriv_succ_const]; rfl
  | succ k=>
    have ht : diagonal (coeff f (k+1) 0)=blockTaylor (k+1) f-blockTaylor k f:= by unfold blockTaylor; rw [Finset.sum_range_succ,add_sub_cancel_left]
    rw [ht, iteratedFDeriv_sub_apply (blockTaylor_contDiff ..|>.contDiffAt) (blockTaylor_contDiff ..|>.contDiffAt),trunc_above h i hi, trunc_above (g:=f) (k:=k) (h.of_le (by exact_mod_cast k.le_succ)) i (by omega), sub_self]
lemma diag_at {f:E→F} (h : ContDiffAt ℝ (↑k) f 0) (hi : j ≤ k) : iteratedFDeriv ℝ j (diagonal (coeff f k 0)) 0=if j=k then iteratedFDeriv ℝ j f 0 else 0 := by
  cases k with
  | zero=>
    rw [show diagonal (coeff f 0 0)=(fun x=> f 0) from funext fun _=> Tensor.coeff_apply_zero f 0 _, show j=0 by omega,if_pos rfl]; ext1 v; simp
  | succ k =>
    have he : diagonal (coeff f (k+1) 0)=blockTaylor (k+1) f -blockTaylor k f:= by unfold blockTaylor; rw [Finset.sum_range_succ,add_sub_cancel_left]
    have hg := h.of_le (show (k:WithTop ℕ∞)≤↑(k+1:ℕ) by exact_mod_cast k.le_succ)
    rw [he,iteratedFDeriv_sub_apply (blockTaylor_contDiff ..|>.contDiffAt) (blockTaylor_contDiff ..|>.contDiffAt),blockTaylor_jets h j hi]
    split
    · rw [trunc_above hg _ (by omega),sub_zero]
    rw [blockTaylor_jets hg _ (by omega),sub_self]
lemma diag_brush {f:E→F} (h : ContDiffAt ℝ k f 0) (hf : normJ k f 0 ≤ C)
    (hp : 0<a) (ht : a ≤ 1) (hk : k < n) (hx : x∈ball 0 a) :
    Brush n ((k+1:ℕ)*(C*a^k)) a⁻¹ (diagonal (coeff f k 0)) x:= by
  have hC : 0≤C := le_trans (norm_nonneg _) hf
  have he:= Shellac.pools (b:=C*a^k) hp ht hk (le_refl 0) (by positivity) (fun x _=> (diag_smooth (coeff f k 0) n).contDiffAt) (fun i hi hj x hx=>by unfold normJ; rw [diagonal_high h hi x,norm_zero]) ?_ x hx
  · simpa using he
  intro i hi; have hu:i ≤ k:= Nat.le_of_lt_succ hi
  unfold normJ; rw [diag_at h hu]
  split
  next he => rw [he]; exact mul_le_mul_of_nonneg_right hf (by positivity)
  rw [norm_zero,zero_mul]; positivity

lemma together (hf : Brush n C d f x) (hg : Brush n v d g x) :
    Brush n ((C*v)*(2:ℝ)^n) d (fun y=> f y*g y) x:= by
  have hx:= hf.paints hg
  refine ⟨hx.smooth,hf.pos,fun j hi=>?_⟩
  refine (hx.order j hi).trans ?_
  rw [← two_mul,mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg hf.nonneg hg.nonneg)) (pow_nonneg hf.pos j)
lemma power (hf : Brush n C d f x) (k : ℕ) : Brush n ((C*2^n)^k) d (fun i=> f i^k) x:= by
  induction k with
  | zero=> simp only [pow_zero]; simpa using! Brush.certified (x:=x) (k:=n) hf.pos (1:ℝ)
  | succ k ih=>
    have he:= together ih hf
    simpa only [pow_succ,mul_assoc] using! he

-- normalize a composition at the radius D on the outer function as well as s on f
lemma pairing {f:E→F} {g:F→H} {k:ℕ} (ha : 0<a) (h : Brush k C a⁻¹ g (f x)) (hf : Brush k a d f x):
    Brush k ((k.factorial*C)*2^k) d (g ∘ f) x := by
  let L : F →L[ℝ] F := a • ContinuousLinearMap.id ℝ F; let g' := g ∘ L; let f' i:= a⁻¹ • f i
  have hh i:L (f' i)= f i:= by unfold L f'; simp [ha.ne']
  have ht : ‖L‖ ≤ a:= by unfold L; rw [norm_smul,Real.norm_of_nonneg ha.le]; exact mul_le_of_le_one_right ha.le ContinuousLinearMap.norm_id_le
  have he := Brush.reading L (show Brush k C a⁻¹ g (L (f' x)) from (hh x).symm ▸ h) ht
  have hr:= hf.smul a⁻¹; rw [norm_inv, Real.norm_of_nonneg ha.le,inv_mul_cancel₀ ha.ne'] at hr
  rw [inv_mul_cancel₀ ha.ne'] at he
  have hq := (hr.pine he); let h' := g' ∘ f'; change Brush k _ _ h' x at hq
  rw [show h'=g ∘ f from funext fun i=> congr_arg g (hh i),one_add_one_eq_two] at hq
  refine ⟨hq.smooth,hf.pos,fun i hi=>?_⟩
  apply (hq.order i hi).trans; rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg (Nat.cast_nonneg _) h.nonneg)) (pow_nonneg hf.pos _)

lemma reprice_exp {g : ℝ→H} {f:E→ℝ} (hf : Brush j p d f x) (hx : 0 < p) (he : p < a) (ht : a ≤ 1) (hg : ∀ y ∈ ball 0 a, Brush n C 1 g y) (hj : j ≤ n) (hk : k < n) :
    Brush j ((j.factorial*(C*a^(k+1)))*2^j) d ((g-blockTaylor k g) ∘ f) x := by
  have ha:= hx.trans he; let z:=g-blockTaylor k g
  have ht:= same_trunc ha ht hk (hg 0 (mem_ball_self ha)).nonneg (fun i hi=> (hg i hi).smooth) (fun i _ hi y hy=> (Brush.offer.1 (hg y hy)).2 i hi) _ (mem_ball_zero_iff.mpr (hf.bound.trans_lt he))
  exact pairing ha (ht.smaller hj) (hf.climb he.le le_rfl)

-- constant with one marker cost, clamp p=0 allowed
lemma constant (he : 0≤d) (h : ‖u‖ ≤ p) : Brush k p d (fun _ : E=>u) x := (Brush.certified he u).climb h le_rfl

lemma on_arc {f:ℝ×E→F} (h : Brush k p d f (v,x)) : Brush k p d (fun x=> f (v,x)) x:= by
  let L:= ContinuousLinearMap.inr ℝ ℝ E; have he:= Lantern.skim (x:=x) (k:=k) (d:=p) (e:=d) (f:=f) (P:=L) (y:=(v,0)) (by simp only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]; exact h) Lantern.n_hook
  simpa [L] using! he
end YM.RGComparison01.AuxCurtain
