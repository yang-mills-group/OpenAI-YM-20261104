import YM.Integration.WilsonMarkedKineticDefect

/-! Finite scalar Taylor data suffice for the true coupling change on every
marked homogeneous rank, including arbitrary inverse field powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedKineticGerm
open Filter Finset FormalBulk08 Wine PowerSeries Comparison.RG02 Adjacent Moving.Path Moving.Shift
open WilsonMarkedKineticDefect
open scoped Topology ContDiff BigOperators Classical

def germ (f : ℝ → ℂ) : PowerSeries ℂ := PowerSeries.mk (motion f)

theorem germ_one : germ (fun _ => (1 : ℂ)) = 1 := by
  ext n
  rw [germ,PowerSeries.coeff_mk,mconst,PowerSeries.coeff_one]

theorem germ_mul {f g : ℝ → ℂ} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    germ (fun x => f x * g x) = germ f * germ g := by
  ext n
  simp only [germ,PowerSeries.coeff_mk,PowerSeries.coeff_mul]
  exact mprod hf hg

theorem germ_pow {f : ℝ → ℂ} (hf : ContDiffAt ℝ ω f 0) (j : ℕ) :
    germ (fun x => f x ^ j) = germ f ^ j := by
  induction j with
  | zero => simpa only [pow_zero] using germ_one
  | succ j ih =>
    simp_rw [pow_succ]
    rw [germ_mul (hf.pow j) hf,ih]

variable (K : UnitCost)
def rate : PowerSeries ℂ := germ (fun t : ℝ => (K.rating t : ℂ))
def reciprocal : PowerSeries ℂ := germ (fun t : ℝ => ((K.rating t)⁻¹ : ℝ))

private theorem smooth_rate : ContDiffAt ℝ ω (fun t : ℝ => (K.rating t : ℂ)) 0 :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp 0 K.smooth
private theorem smooth_recip : ContDiffAt ℝ ω (fun t : ℝ => ((K.rating t)⁻¹ : ℝ) : ℝ → ℂ) 0 :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (K.smooth.inv (by rw [K.origin]; norm_num))

theorem unit : rate K * reciprocal K = 1 := by
  rw [rate,reciprocal,←germ_mul (smooth_rate K) (smooth_recip K),←germ_one]
  apply PowerSeries.ext
  intro n
  simp only [germ,PowerSeries.coeff_mk]
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), K.rating t ≠ 0 :=
    K.smooth.continuousAt.eventually_ne (by rw [K.origin]; norm_num)
  have he : (fun t : ℝ => (K.rating t : ℂ) * ((K.rating t)⁻¹ : ℝ)) =ᶠ[𝓝 0]
      (fun _ => (1 : ℂ)) := hn.mono fun t ht => by
      change (K.rating t : ℂ) * (((K.rating t)⁻¹ : ℝ) : ℂ) = 1
      rw [←Complex.ofReal_mul,mul_inv_cancel₀ ht,Complex.ofReal_one]
  unfold motion Assembly.jet
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]

/-- The physical scalar multiplying a true old homogeneous term is exactly
the finite coefficient of the forward and reciprocal analytic rate series. -/
theorem analytic (C : Caliber) (cap e j r : ℕ) (hj : j ≤ e) :
    physicalWeight C cap e j r =
      coeff (e-j) (rate (C.back cap)^j * reciprocal (C.back cap)^r) := by
  let K := C.back cap
  have h := germ_mul ((smooth_rate K).pow j) ((smooth_recip K).pow r)
  rw [germ_pow (smooth_rate K) j,germ_pow (smooth_recip K) r] at h
  have row := congrArg (coeff (e-j)) h
  rw [physicalWeight,Adjacent.triangular,if_pos hj]
  change _ = coeff (e-j) (rate K^j * reciprocal K^r)
  rw [rate,reciprocal,←row]
  simp only [germ,PowerSeries.coeff_mk,Adjacent.tags,zpow_zero,one_mul,
    Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

/-- Two primitive scalar germs need to agree only through the order being read. -/
def Through (p : ℕ) (A B : PowerSeries ℂ) : Prop := ∀ n ≤ p, coeff n A = coeff n B

private theorem through_mul {p : ℕ} {A B C D : PowerSeries ℂ}
    (h : Through p A B) (k : Through p C D) : Through p (A*C) (B*D) := by
  intro n hn
  rw [coeff_mul,coeff_mul]
  apply sum_congr rfl
  intro ij hi
  have ht : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
  rw [h ij.1 (by omega),k ij.2 (by omega)]

private theorem through_pow {p : ℕ} {A B : PowerSeries ℂ} (h : Through p A B) (k : ℕ) :
    Through p (A^k) (B^k) := by
  induction k with
  | zero => simp only [pow_zero]; exact fun _ _ => rfl
  | succ k ih => simpa only [pow_succ] using through_mul ih h

/-- On the original finite Taylor jet, a separately supplied scalar
kinetic receipt pays both the coupling and ALL reciprocal field factors.
No equality of marked arrays is required to use this theorem. -/
theorem homogeneous (C : Caliber) (cap p : ℕ) (H : Pence)
    (paid : Through p (rate (C.back cap)) (PowerSeries.map Complex.ofRealHom (Wine.bookH H)))
    {j e : ℕ} (he : e ≤ p) (r : ℕ) :
    physicalWeight C cap e j r = formalWeight H e j r := by
  let K := C.back cap
  let A := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
  let U := PowerSeries.map Complex.ofRealHom (Wine.bookU H)
  have u : A*U = 1 := by
    dsimp [A,U]; rw [←map_mul,Wine.book_equal,map_one]
  have hk : Through p (rate K) A := paid
  have k' : Through p (reciprocal K) U := by
    have h : Through p (reciprocal K * (rate K) * U) (reciprocal K * A * U) :=
      through_mul (through_mul (fun _ _ => rfl) hk) (fun _ _ => rfl)
    rw [mul_comm (reciprocal K) (rate K),unit,one_mul,mul_assoc,u,mul_one] at h
    exact fun n hn => (h n hn).symm
  by_cases hj : j ≤ e
  · rw [analytic C cap e j r hj,formalWeight,if_pos hj]
    calc
      _ = coeff (e-j) (A^j*U^r) := through_mul (through_pow hk j) (through_pow k' r) _ (by omega)
      _ = _ := by
        dsimp [A,U,Wine.bill]
        rw [←map_pow,←map_pow,←map_mul,PowerSeries.coeff_map]
        rfl
  · exact (above C cap H (Nat.lt_of_not_ge hj) r).1.trans (above C cap H (Nat.lt_of_not_ge hj) r).2.symm

end YM.Integration.WilsonMarkedKineticGerm
