import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedNullaryGraph
import YM.FVA2.O.Project.Vault
import YM.FVA2.O.Score.Band
import YM.XSpace.FPS

noncomputable section
namespace YM.Integration.AppointedNullaryRefund
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
open PowerSeries YangMills.Matching
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.Scale
open scoped BigOperators Classical

theorem power (c : PowerSeries ℂ) (f : ℕ → ℝ) (hc : ∀ i, coeff i c = (f i : ℂ)) (j k : ℕ) :
    coeff k (c ^ j) = (couplingPower f j k : ℂ) := by
  induction j generalizing k with
  | zero =>
    simp only [pow_zero,coeff_one,couplingPower]
    split <;> simp_all
  | succ j ih =>
    rw [pow_succ',coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i l => coeff i c * coeff l (c^j)),couplingPower]
    rw [Fin.sum_univ_eq_sum_range (fun i => f i * couplingPower f j (k-i)) (k+1)]
    push_cast
    simp_rw [hc,ih]

theorem above (f : ℕ → ℝ) (hf : f 0 = 0) (j k : ℕ) (tooHigh : k < j) : couplingPower f j k = 0 := by
  induction j generalizing k with
  | zero => omega
  | succ j ih =>
    rw [couplingPower]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases atZero : i.val = 0
    · rw [atZero,hf,zero_mul]
    · rw [ih (k-i.val) (by omega),mul_zero]

theorem substituted (c p : PowerSeries ℂ) (f : ℕ → ℝ) (hc : ∀ i, coeff i c = (f i : ℂ))
    (hf : f 0 = 0) (m k : ℕ) (hm : m ≤ k) :
    coeff m (p.subst c) = ∑ j : Fin (k+1), coeff j.val p * (couplingPower f j.val m : ℂ) := by
  have atZero : constantCoeff c = 0 := by rw [← coeff_zero_eq_constantCoeff_apply,hc,hf,Complex.ofReal_zero]
  rw [FPS.coeff_substituted p atZero m,Fin.sum_univ_eq_sum_range
    (fun j => coeff j p * (couplingPower f j m : ℂ)) (k+1)]
  simp_rw [power c f hc]
  change (∑ j ∈ Finset.range (m+1), coeff j p * (couplingPower f j m : ℂ)) = _
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hh : m < i := by
    by_contra hnot
    exact hi (Finset.mem_range.mpr (by omega))
  rw [above f hf i m hh,Complex.ofReal_zero,mul_zero]

variable {G : YM.Gauge}
def assemble (G : YM.Gauge) (h : ℕ) : (Toon G h → ℂ) →ₗ[ℂ] Sec G h where
  toFun u := ∑ t : Toon G h, u t • theory t
  map_add' u v := by
    change (∑ t : Toon G h, (u t + v t) • theory t) = _
    simp only [add_smul,Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum,smul_smul]

theorem oneGrade (F : Scale.Frames G) (H : Civil F) (w h : ℕ) (wh : w ≤ h)
    (u : Grade G w → ℂ) (k : ℕ) :
    (coeff k (F h)) (∑ i : Grade G w, u i • cap (own i) wh) =
      ∑ t : Grade G w, (∑ i : Grade G w, u i * coeff k (_root_.YM.FVA2.O.Score.seats F w i t)) • cap (own t) wh := by
  have each (i : Grade G w) : (coeff k (F h)) (cap (own i) wh) =
      ∑ t : Grade G w, coeff k (_root_.YM.FVA2.O.Score.seats F w i t) • cap (own t) wh := by
    simpa only [report] using (cap_map H (own i) wh k)
  rw [map_sum]
  simp_rw [map_smul,each,Finset.smul_sum,smul_smul,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem action (F : Scale.Frames G) (H : Civil F) (h k : ℕ) (u : Toon G h → ℂ) :
    (coeff k (F h)) (assemble G h u) = assemble G h (fun t : Toon G h =>
      ∑ i : Grade G t.1.val, u ⟨t.1,i⟩ * coeff k (_root_.YM.FVA2.O.Score.seats F t.1.val i t.2)) := by
  change (coeff k (F h)) (∑ t : (w : Fin (h+1)) × Grade G w.val, u t • theory t) =
    ∑ t : (w : Fin (h+1)) × Grade G w.val, (∑ i : Grade G t.1.val, u ⟨t.1,i⟩ * coeff k (_root_.YM.FVA2.O.Score.seats F t.1.val i t.2)) • theory t
  rw [Fintype.sum_sigma,Fintype.sum_sigma,map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact oneGrade F H w.val h (Nat.le_of_lt_succ w.isLt) (fun i => u ⟨w,i⟩) k

theorem price (F : Scale.Frames G) (c : PowerSeries ℂ) (f : ℕ → ℝ)
    (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (p : Bill G)
    (w k : ℕ) (t : Grade G w) :
    coeff k (receipt (_root_.YM.FVA2.O.Score.seats F) (fun i => (p i).subst c) (own t)) =
    ∑ j : Fin (k+1), ∑ b : Fin (k+1), (couplingPower f j.val (k-b.val) : ℂ) *
      ∑ i : Grade G w, coeff j.val (p (own i)) * coeff b.val (_root_.YM.FVA2.O.Score.seats F w i t) := by
  change coeff k (∑ i : Grade G w, (p (own i)).subst c * _root_.YM.FVA2.O.Score.seats F w i t) = _
  rw [map_sum]
  have each (i : Grade G w) :
      coeff k ((p (own i)).subst c * _root_.YM.FVA2.O.Score.seats F w i t) =
      ∑ b : Fin (k+1), coeff b.val (_root_.YM.FVA2.O.Score.seats F w i t) * coeff (k-b.val) ((p (own i)).subst c) := by
    rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun b j => coeff b (_root_.YM.FVA2.O.Score.seats F w i t) * coeff j ((p (own i)).subst c))]
    exact (Fin.sum_univ_eq_sum_range (fun b => coeff b (_root_.YM.FVA2.O.Score.seats F w i t) * coeff (k-b) ((p (own i)).subst c)) (k+1)).symm
  simp_rw [each]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [substituted c _ f hc hf (k-b.val) k (Nat.sub_le _ _),Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem refund (F : Scale.Frames G) (H : Civil F) (c : PowerSeries ℂ) (f : ℕ → ℝ)
    (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (p : Bill G) (h k : ℕ) :
    assemble G h (fun t => coeff k (receipt (_root_.YM.FVA2.O.Score.seats F) (fun i => (p i).subst c) (flash t))) =
      ∑ j : Fin (k+1), ∑ b : Fin (k+1), (couplingPower f j.val (k-b.val) : ℂ) •
        (coeff b.val (F h)) (assemble G h (fun t => coeff j.val (p (flash t)))) := by
  simp_rw [action F H,← map_smul,← map_sum]
  congr 1
  funext t
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using price F c f hc hf p t.1.val k t.2

end YM.Integration.AppointedNullaryRefund

