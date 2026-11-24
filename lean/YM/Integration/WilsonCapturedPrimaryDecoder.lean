import YM.Integration.WilsonCapturedPrimaryPanel

/-! The same fixed left inverse reads the intrinsic physical primary and
the prescribed finite panel. Its price is chosen before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryDecoder
open Function Finset Labels Lattice Wilson RG Source Push.Local
open Next.Foundations Trace.Physical.Germ
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)

/-- All native field tests, including the identity-field component of the frame. -/
def panel : F.Coeff →ₗ[ℂ] ((tests F) → ℂ) :=
  LinearMap.pi fun p => (runProbe F p.val).toLinearMap

private theorem faithful : (panel F).ker=⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y h
  have small := (probe_budget F).choose_spec.choose_spec.2 (x-y) 0 (le_refl 0) (by
    intro p hp
    have eq := congrFun h ⟨p,hp⟩
    change runProbe F p x=runProbe F p y at eq
    simp [map_sub,eq])
  rw [mul_zero] at small
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ((norm_le_size F _).trans small) (norm_nonneg _)))

def decode : ((tests F) → ℂ) →L[ℂ] F.Coeff :=
  ((panel F).exists_leftInverse_of_injective (faithful F)).choose.toContinuousLinearMap

theorem filed (x : F.Coeff) : decode F (panel F x)=x := by
  exact LinearMap.congr_fun ((panel F).exists_leftInverse_of_injective (faithful F)).choose_spec x

theorem size (x : F.Coeff) (z : (tests F) → ℂ) {c : ℝ} (hc : 0≤c)
    (errors : ∀ p, ‖runProbe F p.val x-z p‖≤c) :
    F.coeffSize (x-decode F z)≤(F.extra+1:ℕ)*‖decode F‖*c := by
  have bound : ‖panel F x-z‖≤c := (pi_norm_le_iff_of_nonneg hc).mpr errors
  have eq : x-decode F z=decode F (panel F x-z) := by rw [map_sub,filed]
  refine (size_le_norm F _).trans ?_
  rw [eq,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (((decode F).le_opNorm _).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))) (Nat.cast_nonneg _)

def forecast (y : Probe G d → Polynomial ℂ) : F.Coeff :=
  decode F fun p => (p.val.2.val.factorial : ℂ)*(y p.val).coeff p.val.2.val

def invoice (A : Hol G) (D : ℕ) : ℝ :=
  (F.extra+1:ℕ)*‖decode F‖*∑ p∈tests F,WilsonCapturedPrimaryOriginal.fieldFee A p D

theorem returned (A : Hol G) (D : ℕ) (x : F.Coeff) (y : Probe G d → Polynomial ℂ)
    {L : ℝ} (hl : 0≤L) (each : ∀ p∈tests F,
      ‖runProbe F p x-p.2.val.factorial*(y p).coeff p.2.val‖≤WilsonCapturedPrimaryOriginal.fieldFee A p D*L) :
    F.coeffSize (x-forecast F y) ≤ invoice F A D*L := by
  let M := ∑ p∈tests F,WilsonCapturedPrimaryOriginal.fieldFee A p D
  have pos : 0≤M := sum_nonneg (fun p _ => WilsonCapturedPrimaryPanel.fee_nonneg A p D)
  have bound := size F x (fun p => (p.val.2.val.factorial : ℂ)*(y p.val).coeff p.val.2.val)
    (mul_nonneg pos hl) (fun p => (each p.val p.property).trans (mul_le_mul_of_nonneg_right
      (single_le_sum (fun j _ => WilsonCapturedPrimaryPanel.fee_nonneg A j D) p.property) hl))
  exact bound.trans_eq (by unfold invoice; dsimp only [M];ring)

end YM.Integration.WilsonCapturedPrimaryDecoder
