import YM.Integration.WilsonRootedTwoDateHardRadius

/-! Release the actual signed rows for one nonempty mode at prescribed external radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardMode
open Finset Lattice Wilson RG Marker Overlay LocalComparison LocalComparison.Global
open Push.AbsoluteSums Comparison.Density.RenderM RG3.Script.Picnic
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {Γ : Census V}
    {P : Rep G n} {o : V → Site n} (p : BudgetPoint) (T : Taste X o P Γ)

def row (w : V → ℝ) (z : Γ.Mode) (x : X) (U : Config G n) (i : ℕ × ℕ) : ℝ :=
  if T.menu.marks i.1 i.2=z then Poly.toll w z * p.mass (P.activities.forced i.1).support ‖T.menu.force x i.1 i.2 U‖ else 0

def Released (t κ b : ℝ) : Prop :=
  ∀ w : V → ℝ,(∀ v,0<w v) → ∀ (z : Γ.Mode) (v : V),v∈z.val → ∀ (x : X) (U : Config G n),
    SumBudget (row p T w z x U) ((Poly.toll w z * (t^z.val.card)⁻¹) * (κ*b))

theorem restore {radii : V → ℝ} {t κ b : ℝ} (H : ForcedBudget p T radii κ b)
    (hp : 0<t) (rad : ∀ v,0<radii v) (scale : ∀ z : Γ.Mode,(t^z.val.card)⁻¹ * Poly.toll radii z=1) : Released p T t κ b := by
  intro w h z v seen x U
  let factor := Poly.toll w z * (t^z.val.card)⁻¹
  have pos : 0 ≤ factor := mul_nonneg (Poly.worth h z).le (inv_nonneg.mpr (pow_nonneg hp.le _))
  apply budget_mono (budget_scale pos (H.total v))
  · intro i
    unfold row
    split_ifs
    · exact mul_nonneg (Poly.worth h z).le ((norm_nonneg _).trans (p.loMass _ _ (norm_nonneg _)))
    · exact le_rfl
  · intro i
    unfold row
    by_cases tag : T.menu.marks i.1 i.2=z
    · simp only [tag,seen,if_true]
      have mass : p.mass (P.activities.forced i.1).support ‖T.menu.force x i.1 i.2 U‖ ≤ p.mass (P.activities.forced i.1).support (H.black i) :=
        mul_le_mul_of_nonneg_left (H.forced x i.1 i.2 U) (Real.exp_pos _).le
      calc _ ≤ Poly.toll w z * p.mass (P.activities.forced i.1).support (H.black i) := mul_le_mul_of_nonneg_left mass (Poly.worth h z).le
           _ = factor * (Poly.toll radii z * p.mass (P.activities.forced i.1).support (H.black i)) := by
             dsimp only [factor]
             rw [mul_assoc,←mul_assoc ((t^z.val.card)⁻¹),scale,one_mul]
    · simp only [if_neg tag]
      apply mul_nonneg pos
      split_ifs
      · exact mul_nonneg (Poly.worth rad _).le ((H.black_nonnegative i).trans (p.loMass _ _ (H.black_nonnegative i)))
      · exact le_rfl

end YM.Integration.WilsonRootedTwoDateHardMode
