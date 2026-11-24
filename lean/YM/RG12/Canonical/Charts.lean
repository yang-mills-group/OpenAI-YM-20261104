import YM.Next.UV_STRESS.Least

/-!
# The actual chart behind MatrixTicket.quota (no OPE hypotheses used)

Switch freely at one cutoff between the coordinates read at reference and those at k ≥ ref.
Uniform in the cutoff (above k), not yet in k!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Lattice RG Source
open scoped Topology BigOperators

variable {G : Gauge} (C : Family G)
set_option quotPrecheck false

abbrev UVIndex := ℕ × ℕ
abbrev RepChart (d : ℕ) := C.label d →L[ℂ] C.label d

def mass (d : ℕ) (x : C.label d) := (C.labels.level d).coeffSize x

theorem continuous_mass (d : ℕ) : Continuous (mass C d) := by
  unfold mass Labels.Frame.coeffSize
  fun_prop

theorem mass_le_norm (d : ℕ) (x : C.label d) :
    mass C d x ≤ ((C.labels.level d).extra+1 : ℕ) * ‖x‖ := by
  unfold mass Labels.Frame.coeffSize
  calc
    _ ≤ ∑ _ : (C.labels.level d).Index, ‖x‖ :=
      Finset.sum_le_sum fun i _ => norm_le_pi_norm x i
    _ = _ := by simp [Labels.Frame.Index]

theorem mass_nonneg (d : ℕ) (x : C.label d) : 0 ≤ mass C d x :=
  Finset.sum_nonneg (s:=Finset.univ) fun j _ => norm_nonneg (x j)

theorem norm_le_mass (d : ℕ) (x : C.label d) : ‖x‖ ≤ mass C d x := by
  apply (pi_norm_le_iff_of_nonneg (mass_nonneg ..)).2
  exact fun i => Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)

/-- Declare the linear isomorphism only on the segment where the Based calculus applies. -/
def chartOn (hC : C.Makes) (d k : ℕ) (i : UVIndex) (h₁ : C.ref d ≤ k) (h₂ : k ≤ i.1) :
    C.label d ≃ₗ[ℂ] C.label d :=
  let T := C.factory d i.1 i.2
  let hT : T.Based _ _ _ := hC.calibrated d i.1 i.2 (h₁.trans h₂)
  let S : Module.End ℂ (C.label d) := ((hT.linear k h₁ h₂).1.mk' _).comp
    T.terminal.symm.toLinearMap
  have hinj : Function.Injective S := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro x he
    have hz : ‖x‖ ≤ 0 := by
      obtain ⟨a,-,ha⟩ := Next.UVStress.quota_stop C (D:=d) hC h₁
      apply (ha i.1 i.2 x h₂).trans
      change a * mass C d (S x) ≤ 0
      simp [he, mass, Labels.Frame.coeffSize]
    exact norm_le_zero_iff.mp hz))
  LinearEquiv.ofBijective S ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

def charts (hC : C.Makes) (d k : ℕ) (i : UVIndex) :=
  if h : C.ref d ≤ k ∧ k ≤ i.1 then chartOn C hC d k i h.1 h.2
  else LinearEquiv.refl ℂ (C.label d)

/-- Pull back a k-normalized column to reference. -/
def atK (hC : C.Makes) (d k : ℕ) (i : UVIndex) : RepChart C d :=
  LinearMap.toContinuousLinearMap (charts C hC d k i).symm.toLinearMap

theorem quota_charts (hC : C.Makes) (d k : ℕ) (i : UVIndex) (h₁ : C.ref d ≤ k)
    (h₂ : k ≤ i.1) (x : C.label d) :
    Next.UVStress.quota C d k i.1 i.2 x = mass C d (charts C hC d k i x) := by
  rw [charts, dif_pos ⟨h₁,h₂⟩]; rfl

theorem quota_atK (hC : C.Makes) (d k : ℕ) (i : UVIndex) (h₁ : C.ref d ≤ k)
    (h₂ : k ≤ i.1) (x : C.label d) :
    Next.UVStress.quota C d k i.1 i.2 (atK C hC d k i x) = mass C d x := by
  rw [quota_charts C hC d k i h₁ h₂]
  change mass C d ((charts C hC d k i) ((charts C hC d k i).symm x)) = mass C d x
  rw [LinearEquiv.apply_symm_apply]

theorem atK_fixed_budget (hC : C.Makes) (d k : ℕ) (h₁ : C.ref d ≤ k) :
    ∃ a : ℝ, ∀ i : UVIndex, k ≤ i.1 → ‖atK C hC d k i‖ ≤ a := by
  obtain ⟨a,ha,hx⟩ := Next.UVStress.quota_stop C (D:=d) hC h₁
  refine ⟨a * ((C.labels.level d).extra+1 : ℕ), fun i h₂ => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ha (by positivity))
  intro x
  refine (hx i.1 i.2 _ h₂).trans ?_
  rw [quota_atK C hC _ _ i h₁ h₂, mul_assoc]; exact mul_le_mul_of_nonneg_left (mass_le_norm ..) ha
end YM.RG12
