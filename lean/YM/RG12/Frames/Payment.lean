import YM.RG12.Frames.Flag

/-!
# Upper triangular payments in a moving measuring metric

Allows coefficient data charging full polynomial losses away from the diagonal blocks, and
only a *Fuchsian* price (can use 1+C/positive age) on those blocks; doesn't require the
individual blocks close to identity. The constants refer to the fixed norm of those blocks,
not of their input labels before physical calibration. In particular the step price later can
stay small by *using the same moving currency across adjacent steps*, avoiding per-step norm
conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators

variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]

abbrev Currency (V : Grade d → Type) := ∀ i, V i → ℝ

/-- Permit even non-Hilbert costs for use with finite probes rather than reflection. Need
only subadditivity, positive rescaling and comparison with the fixed norm. -/
structure Fits (g : Currency V) (K : ℝ) : Prop where
  legal : 1 ≤ K
  upper (i x) : g i x ≤ K * ‖x‖
  lower (i x) : ‖x‖ ≤ K * g i x
  subadd (i x y) : g i (x+y) ≤ g i x + g i y
  real_scale (i) (c : ℝ) (hc : 0 ≤ c) x : g i ((c : ℂ) • x) = c * g i x

lemma Fits.nonneg {g : Currency V} {K : ℝ} (h : Fits g K) (i x) : 0 ≤ g i x :=
  nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (h.lower i x)) (zero_lt_one.trans_le h.legal)
lemma Fits.zero {g : Currency V} {K : ℝ} (h : Fits g K) (i) : g i 0 = 0 :=
  ((h.upper i 0).trans (by simp)).antisymm (h.nonneg i 0)

/-- Off-diagonal can use powers of age. Anticipate one *extra* power per degree in the final
l1 costs. `r` refers to a slowly varying price ratio and is NOT engineering dilution. -/
structure Step (A : BlockMatrix V) (outcome income : Currency V) (K s r : ℝ) (p b : ℕ) : Prop where
  basic_o : Fits outcome K
  basic_i : Fits income K
  stays : triangular V A
  diag (i x) : outcome i (block V A i i x) ≤ r ^ p * income i x
  feed (i j : Grade d) (h : i < j) x : outcome i (block V A i j x) ≤ s ^ b * income j x

/-- Exponent convention: the quote's off-diagonal power *plus one* per grade. This pays the
entire transmission cost without any specialized multi-interval induction (and remains
polynomial-log throughout); the missing power lets us use it to pay income at each step with
only polynomial-log accumulation. -/
def price (b : ℕ) (i : Grade d) (s : ℝ) := s ^ (i.val * (b+1))

def coins (b : ℕ) (g : Currency V) (s : ℝ) (x : Col V) := ∑ i, price b i s * g i (x i)

variable {A : BlockMatrix V} {s K r : ℝ} {p b : ℕ} {g h : Currency V}

theorem coin_mono (hg : Fits g K) (hs : 0 ≤ s) (hr : s ≤ r) (x : Col V) :
    coins b g s x ≤ coins b g r x :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hr _) (hg.nonneg i _)

theorem coins_nonneg (hg : Fits g K) (hs : 0 ≤ s) (x : Col V) : 0 ≤ coins b g s x :=
  Finset.sum_nonneg (s:=univ) fun i _ => mul_nonneg (pow_nonneg hs _) (hg.nonneg i (x i))

theorem enlarge (hg : Fits g K) {t : ℝ} (hs : 1 ≤ s) (hr : 1 ≤ r) (ht : t = r*s) (x : Col V) :
    coins b g t x ≤ r ^ (d*(b+1)) * coins b g s x := by
  unfold coins price; subst t; simp_rw [mul_pow]; rw [mul_sum]
  apply sum_le_sum; intro i hi; rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hr (Nat.mul_le_mul_right _ i.is_le)) (pow_nonneg (zero_le_one.trans hs) _)) (hg.nonneg i (x i))

theorem feed_price (hs : 1 ≤ s) (i j : Grade d) (hi : i < j) :
    price b i s * s ^ b ≤ s⁻¹ * price b j s := by
  have h := zero_lt_one.trans_le hs
  rw [inv_mul_eq_div,le_div_iff₀ h]
  unfold price
  have h' : i.val * (b+1)+ (b+1) ≤ j.val * (b+1) := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hi
  calc
    _ = s ^ (i.val * (b+1) + (b+1)) := by rw [mul_assoc,pow_add,pow_succ]
    _ ≤ _ := pow_le_pow_right₀ hs h'

theorem component_cut (hq : Step A g h K s r p b) (hs : 1 ≤ s) (x : Col V)
    (i : Grade d) :
    price b i s * g i ((A x) i) ≤ r ^ p * price b i s * h i (x i) +
      s⁻¹ * coins b h s x := by
  have hp := zero_lt_one.trans_le hs
  have hb : 0 ≤ price b i s := pow_nonneg hp.le _
  rw [block_sum, ← add_sum_erase _ _ (Finset.mem_univ i)]
  have hsg (T : Finset (Grade d)) :
      g i (∑ j ∈ T, block V A i j (x j)) ≤ ∑ j ∈ T, g i (block V A i j (x j)) := by
    induction T using Finset.induction with
    | empty=> simp [hq.basic_o.zero i]
    | insert j T ha IH=>
      rw [sum_insert ha,sum_insert ha]
      exact (hq.basic_o.subadd i _ _).trans (add_le_add le_rfl IH)
  refine (mul_le_mul_of_nonneg_left ((hq.basic_o.subadd ..).trans (add_le_add (hq.diag ..) (hsg _))) hb).trans ?_
  rw [mul_add]; conv_lhs => lhs; rw [← mul_assoc, mul_comm (price b i s)]
  apply add_le_add le_rfl; unfold coins; rw [mul_sum, mul_sum]
  refine (sum_le_sum (g:=fun j : Grade d => s⁻¹ * (price b j s * h j (x j)))
    fun j hj => ?_).trans (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun j _ _ => by
      have h:0 ≤ price b j s := pow_nonneg hp.le _
      exact mul_nonneg (inv_nonneg.mpr hp.le) (mul_nonneg h (hq.basic_i.nonneg _ _)))
  rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with hji|hij
  · rw [hq.stays i j hji _,hq.basic_o.zero]
    rw [mul_zero]; exact mul_nonneg (inv_nonneg.mpr hp.le) (mul_nonneg (pow_nonneg hp.le _) (hq.basic_i.nonneg ..))
  apply (mul_le_mul_of_nonneg_left (hq.feed i j hij _) hb).trans
  simpa only [← mul_assoc] using! (mul_le_mul_of_nonneg_right (feed_price (b:=b) hs i j hij) (hq.basic_i.nonneg j (x j)))

theorem toll_total {s r : ℝ} (hs : 1 ≤ s) (ht : 1+s⁻¹ ≤ r) (p m : ℕ) :
      r^p + (m:ℝ) * s⁻¹ ≤ r^(p+m) := by
    have hp := zero_lt_one.trans_le hs
    have hr := (le_add_of_nonneg_right (inv_nonneg.mpr hp.le) : 1 ≤ 1+s⁻¹).trans ht
    rw [pow_add]
    calc
      _ ≤ r^p * (1+(m:ℝ)*s⁻¹) := by
        rw [mul_add,mul_one]; exact add_le_add le_rfl
          (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hp.le)) (one_le_pow₀ hr))
      _ ≤ _ := mul_le_mul_of_nonneg_left ((one_add_mul_le_pow
        (le_trans (by norm_num : (-2:ℝ) ≤ 0) (inv_nonneg.mpr hp.le)) m).trans
        (pow_le_pow_left₀ (by positivity) ht _)) (by positivity)

theorem Step.pay_all (hq : Step A g h K s r p b) (hs : 1 ≤ s) (ht : 1+s⁻¹ ≤ r) (x : Col V) :
    coins b g s (A x) ≤ r ^ (p+(d+1)) * coins b h s x := by
  have hp := zero_lt_one.trans_le hs
  refine (sum_le_sum (s:=univ) fun i _ => component_cut hq hs x i).trans ?_
  rw [sum_add_distrib]
  simp_rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ]
  simp only [Grade,Fintype.card_fin,mul_assoc,← mul_sum]
  change _ ≤ _*coins b h s x
  exact (le_of_eq (show r^p * coins b h s x + (↑(d+1):ℝ) *(s⁻¹*coins b h s x)=(r^p+↑(d+1)*s⁻¹)*coins b h s x by ring)).trans (mul_le_mul_of_nonneg_right (toll_total hs ht ..) (coins_nonneg hq.basic_i hp.le _))
end YM.RG12.Frames
