import YM.Integration.WilsonMaxwellThermometerFiniteTangent

/-! The finite ground of the three fitted fields is paid on its actual sampling mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseGround

open Filter Function Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement XSpace.Graph3
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Topology Classical

variable {G : Gauge} (W : Initialize G) {V : Store G} (K : Pick V)
    {I : Type} [Fintype I] (basis : Module.Basis I ℂ (Sec G 6))

/-- The price includes every coordinate of the upper and both lower fields. -/
theorem original (simple : G.Simple) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m in Front, ∀ (u : Sec G 6) (P Q : Module.End ℂ (Sec G 4)),
      Equivariant P → Equivariant Q →
      ‖credit W K m u (P (lower G)) (Q (lower G))‖ ≤
        C * m.spacing * cost basis (roster u (P (lower G)) (Q (lower G))) := by
  obtain ⟨C,hC,fee⟩ := WilsonMaxwellThermometerFiniteTangent.full W K basis
  refine ⟨C,hC,?_⟩
  filter_upwards [fee] with m paid
  intro u P Q hP hQ
  simpa only [WilsonMaxwellThermometerCommonTangent.separate K simple u P Q hP hQ, sub_zero]
    using paid u (P (lower G)) (Q (lower G))

/-- Divide only after testing the whole ground on the coarse mesh. -/
theorem restored {A : Type*} (l : Filter A) (simple : G.Simple)
    (mesh : A → Mesh) (axis : A → ℝ) (u : A → Sec G 6) (P Q : A → Module.End ℂ (Sec G 4))
    (cofinal : Tendsto mesh l Front) (hot : ∀ᶠ w in l,0 < axis w)
    (fixed : ∀ᶠ w in l, Equivariant (P w) ∧ Equivariant (Q w))
    (salary : Tendsto (fun w => (mesh w).spacing *
      cost basis (roster (u w) (P w (lower G)) (Q w (lower G))) / axis w) l (𝓝 0)) :
    Tendsto (fun w => credit W K (mesh w) (u w) (P w (lower G)) (Q w (lower G)) /
      (axis w : ℂ)) l (𝓝 0) := by
  obtain ⟨C,_,pays⟩ := original W K basis simple
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [mul_zero] using salary.const_mul C)
  filter_upwards [cofinal.eventually pays, hot, fixed] with w pay pos law
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pos]
  calc
    _ ≤ C*(mesh w).spacing*cost basis (roster (u w) (P w (lower G)) (Q w (lower G)))/axis w :=
      div_le_div_of_nonneg_right (pay _ _ _ law.1 law.2) pos.le
    _ = _ := by ring

end YM.Integration.WilsonOriginalObservedRoseGround
