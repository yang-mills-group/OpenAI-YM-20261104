import YM.Integration.WilsonCapturedPrimaryRays
import YM.Integration.WilsonCapturedPrimaryRough

/-! The original holonomy's angular directions on the retained physical
collar, in the normalized chart used by the true rough derivative estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryAngles
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations Planned.AtomRegular
open WilsonCapturedPrimaryRays WilsonCapturedPrimaryRough
open scoped Classical ContDiff Topology

variable {G : Gauge} {n : Side} {d : ℕ}

def active (o : Site n) (r : ℕ) : Finset (Link n) := univ.filter fun e => separation e.1 o ≤ r

def crop (o : Site n) (r : ℕ) : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi fun e => if e∈active o r then ContinuousLinearMap.proj e else 0

def linkJet (A : Hol G) (P : BudgetPoint) (o : Site n) (p : Probe G d) (j : ℕ) :=
  iteratedDeriv j (testLog A d o (P.threshold • p.1)) 0

def coeff (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d) (j : ℕ) :
    Directions G n := (suppress (quadratic P) o)
      (crop o r ((j.factorial:ℝ)⁻¹ • linkJet A P o p j))

def angular (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d) (t : ℝ) :
    Directions G n := ∑ j∈range (d+1), t^j • coeff A P o r p j

private theorem angled (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ)
    (p : Probe G d) (t : ℝ) :
    angular A P o r p t =
      suppress (quadratic P) o (crop o r (polynomial d (testLog A d o (P.threshold • p.1)) t)) := by
  simp [angular,polynomial,coeff,linkJet,map_sum]

private theorem cut_apply (o : Site n) (r : ℕ) (u : Directions G n) (e : Link n) :
    crop o r u e = if e∈active o r then u e else 0 := by
  by_cases he : e∈active o r <;> simp [crop,he]

private theorem cut_output (o : Site n) (r : ℕ) (u : Directions G n) :
    WilsonCapturedPrimaryCollar.clip o r (increment 1 u) = increment 1 (crop o r u) := by
  funext e
  by_cases h : separation e.1 o ≤ r <;>
    simp [WilsonCapturedPrimaryCollar.clip,increment,cut_apply,active,h]

theorem physical (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d) (t : ℝ) :
    field A P o r p t = bone (quadratic P) o (active o r) (angular A P o r p t) := by
  rw [field,cut_output,angled,bone]
  congr 1
  funext e
  by_cases h : e∈active o r <;> simp [limitAmp,cut_apply,suppress_apply,h,smul_smul,
    (weight_pos (quadratic P) o e).ne']

def linkFee (A : Hol G) (p : Probe G d) (j : ℕ) := (testLog_bound A d j p.1).choose

theorem coeff_price (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    (j : ℕ) (hj : j≤d) :
    ‖coeff A P o r p j‖ ≤ linkFee A p j*(1+(r:ℝ))^d := by
  have fee_pos := (testLog_bound A d j p.1).choose_spec.1
  have hR : 1 ≤ 1+(r:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have price0 : 0 ≤ linkFee A p j*(1+(r:ℝ))^d := mul_nonneg fee_pos.le (pow_nonneg (by positivity) _)
  apply (pi_norm_le_iff_of_nonneg price0).mpr
  intro e
  rw [coeff,suppress_apply,cut_apply]
  by_cases inside : e∈active o r
  · rw [if_pos inside,Pi.smul_apply,norm_smul,norm_smul]
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos (weight_pos ..),Real.norm_eq_abs,abs_inv,
      abs_of_pos (by exact_mod_cast j.factorial_pos : (0:ℝ)<j.factorial)]
    have he1 : (1:ℝ) ≤ 1+(separation e.1 o:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) (separation e.1 o)]
    have hwt : P.threshold ≤ weight (quadratic P) o e :=
      le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ he1)
    have hfac : (j.factorial:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast j.factorial_pos)
    have hj' : j-1 ≤ d := by omega
    have dist : separation e.1 o ≤ r := (mem_filter.mp inside).2
    have dd : (1:ℝ)+(separation e.1 o:ℝ) ≤ 1+(r:ℝ) := by exact_mod_cast Nat.add_le_add_left dist 1
    have sp : (1+(separation e.1 o:ℝ))^(j-1) ≤ (1+(r:ℝ))^d :=
      (pow_le_pow_left₀ (by positivity) dd _).trans
        (pow_le_pow_right₀ hR hj')
    have native := (testLog_bound A d j p.1).choose_spec.2 n o e P.threshold
      P.threshold_pos.le P.threshold_le
    change ‖linkJet A P o p j e‖ ≤ linkFee A p j*P.threshold*(1+(separation e.1 o:ℝ))^(j-1) at native
    calc
      _ ≤ (weight (quadratic P) o e)⁻¹ *
          (linkFee A p j*weight (quadratic P) o e*(1+(r:ℝ))^d) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (weight_pos ..).le)
        exact ((mul_le_of_le_one_left (norm_nonneg _) hfac).trans native).trans
          (mul_le_mul (mul_le_mul_of_nonneg_left hwt fee_pos.le) sp
            (pow_nonneg (by positivity) _) (mul_nonneg fee_pos.le (weight_pos ..).le))
      _ = _ := by field_simp [(weight_pos (quadratic P) o e).ne']
  · simpa only [if_neg inside,smul_zero,norm_zero] using price0

theorem centered (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d) :
    coeff A P o r p 0 = 0 := by simp [coeff,linkJet,testLog_zero]

private def count (d j : ℕ) : ℝ := ∑ ℓ∈range (d+2), (j.descFactorial ℓ:ℝ)

private theorem count_ge (d j ℓ : ℕ) (h : ℓ ≤ d+1) : (j.descFactorial ℓ:ℝ) ≤ count d j :=
  single_le_sum (s:=range (d+2)) (fun k _ => Nat.cast_nonneg (j.descFactorial k))
    (mem_range.mpr (by omega))

def panelFee (A : Hol G) (p : Probe G d) : ℝ :=
  ∑ j∈range (d+1), count d j * linkFee A p j

def wallet (A : Hol G) (p : Probe G d) (r : ℕ) := 1+panelFee A p*(1+(r:ℝ))^d

theorem wallet_one (A : Hol G) (p : Probe G d) (r : ℕ) : 1 ≤ wallet A p r := by
  have hf : 0 ≤ panelFee A p := sum_nonneg fun i _ => mul_nonneg
    (by unfold count; positivity) (testLog_bound A d i p.1).choose_spec.1.le
  exact le_add_of_nonneg_right (mul_nonneg hf (pow_nonneg (by positivity) _))

theorem derivatives (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    {t : ℝ} (h : |t| ≤ 1) (k : ℕ) (hk : k ≤ d+1) :
    ‖iteratedFDeriv ℝ k (angular A P o r p) t‖ ≤ wallet A p r := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold angular
  rw [iteratedDeriv_fun_sum (I:=range (d+1))
    (f:=fun j (s:ℝ) => s^j • coeff A P o r p j) (fun i _ => by fun_prop)]
  calc
    _ ≤ ∑ j∈range (d+1), count d j * linkFee A p j * (1+(r:ℝ))^d := by
      apply (norm_sum_le ..).trans
      refine sum_le_sum fun j hj => ?_
      rw [iteratedDeriv_smul_const (by fun_prop : ContDiffAt ℝ k (fun s : ℝ => s^j) t),
        iteratedDeriv_pow,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow]
      rw [mul_assoc (count d j)]
      exact mul_le_mul ((mul_le_of_le_one_right (Nat.cast_nonneg _)
        (pow_le_one₀ (abs_nonneg _) h)).trans (count_ge d j k hk))
        (coeff_price A P o r p j (Nat.le_of_lt_succ (mem_range.mp hj))) (norm_nonneg _)
        (by unfold count; positivity)
    _ ≤ _ := by rw [←Finset.sum_mul]; unfold wallet panelFee; linarith

theorem size (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    {t : ℝ} (h : |t| ≤ 1) : ‖angular A P o r p t‖ ≤ |t| *wallet A p r := by
  unfold angular
  have bound : ‖∑ j∈range (d+1), t^j • coeff A P o r p j‖ ≤
      ∑ j∈range (d+1), |t| *(count d j * linkFee A p j * (1+(r:ℝ))^d) := by
    refine (norm_sum_le ..).trans (sum_le_sum (fun j hj => ?_))
    have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
    have fj : 0≤linkFee A p j := (testLog_bound A d j p.1).choose_spec.1.le
    by_cases z : j=0
    · rw [z,centered,smul_zero,norm_zero]
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by unfold count; positivity)
        (testLog_bound A d 0 p.1).choose_spec.1.le) (pow_nonneg (by positivity) _))
    · rw [norm_smul,Real.norm_eq_abs,abs_pow]
      have count1 : 1 ≤ count d j := by
        simpa only [Nat.descFactorial_zero,Nat.cast_one] using (count_ge d j 0 (Nat.zero_le _))
      exact mul_le_mul (pow_le_of_le_one (abs_nonneg _) h z)
        ((coeff_price A P o r p j hj').trans (mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left fj count1) (pow_nonneg (by positivity) _)))
        (norm_nonneg _) (abs_nonneg _)
  rw [←Finset.mul_sum,←Finset.sum_mul] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (by unfold wallet panelFee; linarith) (abs_nonneg _))

end YM.Integration.WilsonCapturedPrimaryAngles
