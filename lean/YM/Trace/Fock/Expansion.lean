import YM.Trace.Fock.Coherent
import Mathlib.Analysis.Normed.Group.Tannery
/-!
Cancel the common Gaussian and polarize the relative vacuum matrix identity. No
operators on arbitrary number-sector vectors need be multiplied. Symmetry is
later used only to desymmetrize the tested tensors.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Trace.Shell
open YM Boundary Function Filter Set Complex MeasureTheory
open scoped BigOperators Topology InnerProductSpace Pointwise
variable {m n : ℕ}
variable (h : SlotField m) (s : ℝ)

lemma jet_scale (z : ℂ) (p : Mom) : jet p (z • h)=z • jet p h := by
    ext1 i; unfold jet; simp only [PiLp.smul_apply]
    simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl
    intro i _; rw [Pi.smul_apply]; simp_rw [map_smul,smul_apply]; rw [smul_comm z ‖p‖,smul_comm z ((projKernel _ _ _))]
lemma product_scale (z : ℂ) (p : Cords n) : productTest (z • h) p=z^n • productTest h p := by
    ext1 I; unfold productTest rawTensor; simp only [PiLp.smul_apply,jet_scale,smul_eq_mul,Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_fin]
lemma slot_scaled (z : ℂ) : slot (z • h) n = z^n • slot h n := by
    apply Lp.ext
    filter_upwards [evaluate_slot (z • h) (n:=n), Lp.coeFn_smul (z^n) (slot h n), evaluate_slot h (n:=n)] with x hx hy hb
    rw [hx,hy]; change _=z^n • (slot h n) x; rw [hb,product_scale h z]

lemma factor_neg (h : SlotField m) : pulseFactor (-h) = pulseFactor h := by
    unfold pulseFactor; rw [show (-h : SlotField m)=(-1:ℂ) • h from (neg_one_smul ℂ h).symm,slot_scaled]
    simp
lemma ElectricTest.scale (s : ℝ) (h : SlotField m) (ht : ElectricTest h) : ElectricTest ((s:ℂ) • h) := fun i => by
    rw [Pi.smul_apply]; refine ⟨DFunLike.ext _ _ (fun x=>?_),(ht i|>.2.comp_left (show (s:ℂ) • (0:ℂ)=0 from smul_zero _))⟩
    rw [Probe.bar_at,smul_apply,smul_eq_mul,star_mul', RCLike.star_def,conj_ofReal];
    simp only [starRingEnd_apply, ← Probe.bar_at, (ht i).1]
lemma support_scale (z : ℂ) (h : SlotField m) : supportE (z • h) ⊆ supportE h := iUnion_subset (fun i =>
    (tsupport_comp_subset (g:=fun (t:ℂ)=>z • t) (smul_zero _) (⇑(h i))).trans (subset_iUnion (fun j => tsupport (h j)) i))

lemma spin_flip (n : ℕ) : star (coefficient n * (-1)^n) = coefficient n := by
    unfold coefficient
    have hc : ((starRingEnd ℂ) I)^n * (-1)^n=I^n := by rw [← mul_pow]; simp
    simp only [star_def,map_mul,map_inv₀,map_pow,conj_ofReal,map_neg,map_one]
    rw [mul_assoc,mul_comm (((Real.sqrt (n.factorial:ℝ)):ℂ)⁻¹) ..,← mul_assoc,hc] -- test

private lemma tsum_exception (z : ℂ) (t : ℝ) (hz : z=(t:ℂ)) : star z=z := by rw [hz]; exact Complex.conj_ofReal _
lemma sail_ahead (k:SlotField m) (s:ℂ) : sail (s • k) n=(s^n) • (sail k n) := by
    simp only [sail_eval]
    rw [slot_scaled]; exact smul_comm .. -- names

/- Elementary scalar-series uniqueness under absolute summability on one real interval. -/
lemma powers_unique (a:ℕ→ℂ) (h : ∀ s : ℝ, HasSum (fun n=> (s:ℂ)^n*a n) 0) : ∀ n, a n=0 := by
   have hT : Summable (fun n => ‖a n‖) := by have := (h 1).summable; simpa using this.norm
   have htzero (n:ℕ) : (∑'i:ℕ, (↑(0:ℝ):ℂ)^i * a (i+n)) = a n := by
      refine (tsum_eq_single (β:=ℕ) 0 fun i hi=> ?_).trans ?_ <;> simp [*]
   suffices he : ∀ k (s : ℝ), ∑' (n : ℕ), (s:ℂ)^n*a (n+k) = 0 by
      intro n; simpa using (he n 0 ▸ htzero n).symm -- use zero
   intro k
   induction k with
   | zero => exact fun s=> (h s).tsum_eq
   | succ k ih =>
      let g := fun (s:ℝ) => ∑' (n : ℕ), (s:ℂ)^n*a (n+k+1)
      have h0 : a k=0 := by simpa [htzero] using! (show a k=0 from (htzero k).symm.trans (ih 0))
      have HG (s : ℝ) (hs : s ≠ 0) : g s=0 := by
         have hS := (summable_nat_add_iff (f:=fun i => (s:ℂ)^i * a i) k).mpr ((h s).summable)
         have hh := hS.tsum_eq_zero_add
         simp_rw [show ∀ i : ℕ, (s:ℂ)^(i+k)*a (i+k) = (s:ℂ)^k * ((s:ℂ)^i*a (i+k)) from fun i => by rw [pow_add]; ring, show ∀ i : ℕ, ((s:ℂ)^k) * ((s:ℂ)^(i+1)*a (i+1+k))=((s:ℂ)^k)*s*((s:ℂ)^i*a (i+k+1)) from fun i=> by rw [pow_succ,show i+1+k=i+k+1 from by omega]; ring,tsum_mul_left,ih s] at hh -- test
         have hhead : (s:ℂ)^k*a k=0 := by rw [h0,mul_zero]
         rw [pow_zero,zero_add,one_mul,hhead,mul_zero,zero_add] at hh
         exact mul_left_cancel₀ (a:=((s:ℂ)^k)*(s)) (by exact mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr hs)) (ofReal_ne_zero.mpr hs)) (by simpa [← Nat.add_assoc] using hh.symm)
      suffices HG0 : g 0=0 by intro s; by_cases hs : s=0; rw [hs]; exact HG0; exact HG s hs
      have ht := tendsto_tsum_of_dominated_convergence (f:=fun s:ℝ => fun n:ℕ => (s:ℂ)^n*a (n+k+1)) (g:=fun n:ℕ => (↑(0:ℝ):ℂ)^n*a (n+k+1)) (𝓕:=𝓝[>] 0)
        (bound:=fun n:ℕ => ‖a (n+k+1)‖) (by simp_rw [Nat.add_assoc]; exact (summable_nat_add_iff (k+1)).mpr hT)
        (fun n => Filter.Tendsto.mono_left ((Complex.continuous_ofReal.tendsto (0:ℝ)|>.pow n).mul_const _) nhdsWithin_le_nhds)
      have Ht : Tendsto g (𝓝[>]0) (𝓝 (g 0)) := ht (by
         filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with s hs hu
         intro n; have hs' : s>0 := hs; have ht' : s<1 := hu
         rw [norm_mul]; apply mul_le_of_le_one_left (by positivity : 0≤‖a (n+k+1)‖) (by rw [norm_pow]; norm_cast; rw [Real.norm_of_nonneg hs'.le]; exact pow_le_one₀ hs'.le ht'.le ) )
      have HN : Tendsto g (𝓝[>]0) (𝓝 (0:ℂ)) := (tendsto_const_nhds (x:=(0:ℂ))).congr' ((eventually_mem_nhdsWithin).mono fun s (hs:0<s)=> (HG s (by linarith)).symm)
      exact tendsto_nhds_unique Ht HN
variable (x y : Sum m)
lemma pulse_identity_terms (n : ℕ) (idn : ∀ s : ℝ, inner ℂ (pulse (-((s:ℂ) • h))) x = inner ℂ y (pulse ((s:ℂ) • h))) :
    inner ℂ (slot h n) (x n) = inner ℂ (y n) (slot h n) := by
    have H0 (s : ℝ) : inner ℂ (sail ((s:ℂ) • -h)) x=inner ℂ y (sail ((s:ℂ) • h)) := by
       have H := idn s
       unfold pulse at H; rw [factor_neg,inner_smul_left,inner_smul_right,conj_ofReal] at H
       have he := mul_left_cancel₀ (ofReal_ne_zero.mpr (pulseFactor_pos _).ne') H
       convert he using 2; rw [smul_neg]
    let A k := inner ℂ (sail (-h) k) (x k) - inner ℂ (y k) (sail h k)
    have hsm := (lp.summable_inner (𝕜:=ℂ) (sail (-h)) (g:=x))
    have hsm' := (lp.summable_inner (𝕜:=ℂ) y (sail h))
    have ha (k : ℕ) : star (coefficient k) * inner ℂ (slot (-h) k) (x k) = coefficient k * inner ℂ (slot h k) (x k) := by
            rw [show (-h) = (-1:ℂ) • h from (neg_one_smul ℂ h).symm,slot_scaled,inner_smul_left]; simp only [← star_def, ← mul_assoc,← star_mul',spin_flip]
    have he (s : ℝ) (k : ℕ) : let z := (s:ℂ) • h;
                                inner ℂ (sail (-z) k) (x k) - inner ℂ (y k) (sail z k) = (s:ℂ)^k * A k := by
        intro z; dsimp only [z,A]; rw [← smul_neg]; 
        rw [sail_ahead,sail_ahead (s:=s) h,inner_smul_left,inner_smul_right, ← ofReal_pow,conj_ofReal]
        ring
    have hc (s : ℝ) : HasSum (fun k:ℕ => (s:ℂ)^k * A k) 0 := by
        have hl := (lp.hasSum_inner (𝕜:=ℂ) (sail ((s:ℂ) • -h)) x).sub ((lp.hasSum_inner y (sail ((s:ℂ) • h))))
        rw [H0 s,sub_self] at hl
        simp only [smul_neg,he s] at hl; exact hl
    have hp := sub_eq_zero.mp (powers_unique A hc n)
    change inner ℂ (coefficient n • _) _ = inner ℂ _ (coefficient n • _) at hp
    rw [inner_smul_left,inner_smul_right, show starRingEnd ℂ (coefficient n)=star (coefficient n) from rfl, ha n] at hp
    exact mul_left_cancel₀ (by unfold coefficient; exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (inv_ne_zero (ofReal_ne_zero.mpr (by positivity)))) hp
end YM.Trace.Shell
