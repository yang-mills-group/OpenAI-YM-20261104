import YM.Integration.FVA1Physical.ActualPush
import YM.Integration.FVA1Physical.Round2.MeanResponseJets

/-! Held derivatives in a selected physical history, with the actual
 incoming and outgoing vacuum factors and the conditional mean of the
 incoming marked error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical
open Lattice Wilson RG MeasureTheory Push.Local.Kernel
open scoped Classical BigOperators
variable {G : Gauge}

theorem conditional_mean_jets (A : History G) (selected : A.Selected) {N n m : ℕ}
    (hi : m<N) (F : Config G (A.S.side (m+1) n) → ℂ)
    (hf : Integrable (fun U => (A.rep N n (m+1)).eval U • F U) (prior G (A.S.side (m+1) n)))
    (X : Edges (A.S.side m n)) (V : Config G (A.S.side m n))
    (k : ℕ) {r : ℝ} (hr : 0≤r) (l : List (Directions G (A.S.side m n))) (hl : l.length≤k)
    (hs : ∀ v∈l, ∀ e∉X, v e=0) (hb : ∀ v∈l, ∀ e∈X, ‖v e‖≤r) :
    let S := A.levels.clock.op m n
    let β := A.β N n (m+1)
    ‖leftDerivs (conditionalPush A N n m F) l V‖ ≤
      responsePrice G (β*S.kernel.penalty) k X.card r *
        conditionalPush A N n m (fun U=>‖F U‖) V := by
  intro S β
  let D := (A.rep N n (m+1)).eval
  let Z := (A.rep N n m).eval
  let B := fun U => D U • F U
  have hD : Integrable D (prior G (A.S.side (m+1) n)) :=
    ((A.rep N n (m+1)).envelope (selected.represents N n (m+1) hi).good).integrable _
  have hp (U) : 0<D U := SectorNext.Vacuum.strictly A selected N n (m+1) hi U
  have hout : Z = S.push β D := (selected.steps N n m hi).1
  have hx : conditionalPush A N n m F = fun U => S.push β B U / ((S.push β D U : ℝ) : ℂ) := by
    funext U
    change (Z U)⁻¹ • S.push β B U = _
    rw [hout,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  have hm : (fun U=>‖B U‖) = (fun U=>D U • ‖F U‖) := by
    funext U
    simp only [B,norm_smul,Real.norm_of_nonneg (hp U).le,smul_eq_mul]
  rw [hx]
  have bound := sparse_response_mean S β X V (A.levels.blocks m n).branches hD hf hp hr k l hl hs hb
  apply bound.trans_eq
  change _ = _ * ((Z V)⁻¹ * S.push β (fun U=>D U • ‖F U‖) V)
  rw [hout,←hm,div_eq_mul_inv,mul_comm ((S.push β D V)⁻¹)]
end YM.Integration.FVA1Physical
