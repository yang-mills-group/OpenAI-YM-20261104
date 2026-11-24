import YM.RG.Bounded

/-! Signed covariance under two positive conditionally normalized Haar
densities on the same retained fibre. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredHaarReading

open MeasureTheory RG
open scoped Classical

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

def mean (d : X → ℝ) (A : X → ℂ) : ℂ := ∫ z, d z • A z ∂ν

def cov (d : X → ℝ) (A B : X → ℂ) : ℂ :=
  mean ν d (fun z => A z * B z) - mean ν d A * mean ν d B

theorem product {A B : X → ℂ} (a : Envelope A) (b : Envelope B) :
    Envelope (fun z => A z * B z) := by
  obtain ⟨a₀,ha⟩ := a.cost
  obtain ⟨b₀,hb⟩ := b.cost
  exact ⟨a.meas.mul b.meas, a₀*b₀, fun z => by
    rw [norm_mul]; exact mul_le_mul (ha z) (hb z) (norm_nonneg _) ((norm_nonneg _).trans (ha z))⟩

theorem centered {A : X → ℂ} (a : Envelope A) (u : ℂ) : Envelope (fun z => A z-u) := by
  obtain ⟨v,hv⟩ := a.cost
  exact ⟨a.meas.sub measurable_const,v+‖u‖,fun z => (norm_sub_le ..).trans (add_le_add (hv z) (le_refl ‖u‖))⟩

private theorem sampled {d : X → ℝ} (hd : Integrable d ν) {A : X → ℂ} (h : Envelope A) :
    Integrable (fun z => d z • A z) ν := by
  obtain ⟨v,hv⟩ := h.cost
  apply Integrable.mono' (hd.norm.mul_const v) (hd.aestronglyMeasurable.smul h.meas.aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖d z • A z‖ ≤ ‖d z‖ * v
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hv z) (norm_nonneg _)

private theorem translate {d : X → ℝ} (hd : Integrable d ν) (one : ∫ z,d z ∂ν = 1)
    {A : X → ℂ} (a : Envelope A) (u : ℂ) : mean ν d (fun z => A z-u) = mean ν d A-u := by
  have c : Envelope (fun _ : X => u) := ⟨measurable_const, ‖u‖, fun _ => le_rfl⟩
  simp only [mean, smul_sub]
  rw [integral_sub (sampled ν hd a) (sampled ν hd c)]
  simp only [Complex.real_smul, integral_mul_const, integral_complex_ofReal, one,
    Complex.ofReal_one, one_mul]

private theorem right {d : X → ℝ} (hd : Integrable d ν) (one : ∫ z,d z ∂ν = 1)
    {A B : X → ℂ} (a : Envelope A) (b : Envelope B) (u : ℂ) :
    cov ν d A (fun z => B z-u) = cov ν d A B := by
  have h : (fun z => d z • (A z * (B z - u))) =
      (fun z => d z • (A z * B z) - (d z • A z) * u) := by
    funext z; simp only [Complex.real_smul]; ring
  unfold cov
  rw [translate ν hd one b u]
  unfold mean
  rw [h, integral_sub (sampled ν hd (product a b)) ((sampled ν hd a).mul_const u), integral_mul_const]
  ring

private theorem symmetric (d : X → ℝ) (A B : X → ℂ) : cov ν d A B = cov ν d B A := by
  simp only [cov, mul_comm]

private theorem shift {d : X → ℝ} (hd : Integrable d ν) (one : ∫ z,d z ∂ν = 1)
    {A B : X → ℂ} (a : Envelope A) (b : Envelope B) (u v : ℂ) :
    cov ν d (fun z => A z-u) (fun z => B z-v) = cov ν d A B := by
  rw [right ν hd one (centered a u) b v, symmetric ν d _ B, right ν hd one b a u, symmetric ν d B A]

private theorem change {w p : X → ℝ} (hw : Integrable w ν) (hp : Integrable p ν)
    {A : X → ℂ} (a : Envelope A) :
    mean ν w A - mean ν p A = ∫ z,(w z-p z) • A z ∂ν := by
  simp only [mean, sub_smul, integral_sub (sampled ν hw a) (sampled ν hp a)]

/-- Three actual signed readings suffice. Their errors can use independent
absolute centered moments, including the covariance product itself. -/
theorem compared {w p : X → ℝ} (hw : Integrable w ν) (hp : Integrable p ν)
    (w1 : ∫ z,w z ∂ν = 1) (p1 : ∫ z,p z ∂ν = 1)
    {A B : X → ℂ} (a : Envelope A) (b : Envelope B) {cost qa qb : ℝ}
    (joint : ‖∫ z,(w z-p z) • ((A z-mean ν p A)*(B z-mean ν p B)) ∂ν‖ ≤ cost)
    (old : ‖∫ z,(w z-p z) • (A z-mean ν p A) ∂ν‖ ≤ qa)
    (fresh : ‖∫ z,(w z-p z) • (B z-mean ν p B) ∂ν‖ ≤ qb) :
    ‖cov ν w A B - cov ν p A B‖ ≤ cost+qa*qb := by
  let f := fun z => A z - mean ν p A
  let g := fun z => B z - mean ν p B
  have hf : Envelope f := centered a _
  have hg : Envelope g := centered b _
  have f0 : mean ν p f = 0 := (translate ν hp p1 a _).trans (sub_self _)
  have g0 : mean ν p g = 0 := (translate ν hp p1 b _).trans (sub_self _)
  have x : ‖mean ν w f‖ ≤ qa := by
    rw [← change ν hw hp hf, f0, sub_zero] at old
    exact old
  have y : ‖mean ν w g‖ ≤ qb := by
    rw [← change ν hw hp hg, g0, sub_zero] at fresh
    exact fresh
  rw [← change ν hw hp (product hf hg)] at joint
  rw [← shift ν hw w1 a b (mean ν p A) (mean ν p B), ← shift ν hp p1 a b (mean ν p A) (mean ν p B)]
  change ‖cov ν w f g - cov ν p f g‖ ≤ _
  simp only [cov, f0, g0, zero_mul, sub_zero]
  rw [sub_right_comm]
  apply (norm_sub_le ..).trans
  rw [norm_mul]
  exact add_le_add joint (mul_le_mul x y (norm_nonneg _) ((norm_nonneg _).trans x))

end YM.Integration.WilsonCenteredHaarReading

