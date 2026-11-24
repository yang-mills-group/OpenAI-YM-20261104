import YM.Integration.WilsonThermometerCenteredAlgebra

/-! The second and third powers of the paid proper-face error on the
three-name Wilson source census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredBound
open Finset Marker QuadraticLocal WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

private theorem different : full ≠ (J).quiet := by
  intro e
  exact univ_nonempty.ne_empty (congrArg Subtype.val e : (univ : Finset (Fin 3))=∅)

theorem proper_faces (M : Poly J) (mu : M.part (J).quiet=1) :
    (proper M).part (J).quiet=0 ∧ (proper M).part full=0 ∧
    ∀ s : (J).Mode, s≠(J).quiet → s≠full → (proper M).part s=M.part s := by
  refine ⟨?_,?_,?_⟩
  · simp [proper,sub_eq_add_neg,Poly.part_send,mu,Ne.symm different]
  · simp [proper,sub_eq_add_neg,Poly.part_send,different]
  · intro s q f
    simp [proper,sub_eq_add_neg,Poly.part_send,q,f]

theorem charged (F Q : Poly J) (fu : F.part (J).quiet=1) (qu : Q.part (J).quiet=1)
    (w : Fin 3 → ℝ) (hw : ∀ i,0<w i) {e : ℝ}
    (pr : Poly.price w (proper (total F Q))≤e) :
    Poly.toll w full * ‖(Extra.Trajectories.connected F).part full -
      (Extra.Trajectories.connected Q).part full - (total F Q).part full‖ ≤ e^2/2+e^3/3 := by
  let E := proper (total F Q)
  have fee (k : ℕ) : Poly.toll w full * ‖(E^k).part full‖ ≤ e^k :=
    (Poly.member hw full _).trans ((Poly.powers hw E k).trans
      (pow_le_pow_left₀ (Poly.nonnegative hw E) pr k))
  rw [WilsonThermometerCenteredAlgebra.connected F Q fu qu]
  have terms : (total F Q).part full - (2:ℂ)⁻¹*(E^2).part full + (3:ℂ)⁻¹*(E^3).part full -
      (total F Q).part full = -((2:ℂ)⁻¹*(E^2).part full)+(3:ℂ)⁻¹*(E^3).part full := by abel
  rw [terms]
  calc
    _ ≤ Poly.toll w full * (‖-((2:ℂ)⁻¹*(E^2).part full)‖+‖(3:ℂ)⁻¹*(E^3).part full‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le ..) (Poly.worth hw full).le
    _ = (Poly.toll w full * ‖(E^2).part full‖)/2 + (Poly.toll w full * ‖(E^3).part full‖)/3 := by
      norm_num [norm_mul,norm_inv]; ring
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (fee 2) (by norm_num))
      (div_le_div_of_nonneg_right (fee 3) (by norm_num))

theorem proper_bill (M : Poly J) (mu : M.part (J).quiet=1) (w : Fin 3 → ℝ) :
    Poly.price w (proper M) =
      ∑ s : (J).Mode, if s≠(J).quiet ∧ s≠full then Poly.toll w s * ‖M.part s‖ else 0 := by
  obtain ⟨q,f,each⟩ := proper_faces M mu
  apply sum_congr rfl
  intro s _
  by_cases he : s=(J).quiet
  · simp [he,q]
  by_cases hf : s=full
  · simp [hf,f]
  simp [he,hf,each s he hf]

end YM.Integration.WilsonThermometerCenteredBound
