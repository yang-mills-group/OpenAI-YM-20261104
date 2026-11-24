import YM.Integration.FVA1Physical.Round2.FieldDerivativeReserve
import YM.MSbar.Whisk.Muse

/-! Upgrade small errors at individually tested derivative words to their
absolute rooted sum, uniformly in the period and the tests. `major` carries
the stronger support weight and `kernel` pays its change of exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset MSbar.Whisk
open scoped Classical BigOperators
variable {σ:Type} [Fintype σ]

theorem rooted_word_trade (q:ℕ) (err weight major kernel : List σ→ℝ) {ε M D τ:ℝ}
    (hτ:0<τ) (hε:0≤ε)
    (words:∀ l, l.length=q → 0 ≤ err l ∧ err l ≤ ε ∧ 0 < weight l ∧ 0 ≤ major l ∧
      0≤kernel l ∧ weight l ^ 2 ≤ major l*kernel l)
    (bank:Yarn q (fun l=>err l*major l)≤M) (geometry:Yarn q kernel≤D) :
    Yarn q (fun l=>err l*weight l) ≤ τ*M+(ε/τ)*D := by
  have share (l:List σ) (hl:l.length=q) :
      err l*weight l ≤ τ*(err l*major l)+(ε/τ)*kernel l := by
    obtain ⟨ed,small,wp,hp,kp,relation⟩:=words l hl
    by_cases heavy:weight l≤τ*major l
    · have h:=mul_le_mul_of_nonneg_left heavy ed
      linarith only [h,mul_nonneg (div_nonneg hε hτ.le) kp]
    have fine : τ*weight l ≤ kernel l := by
      apply (mul_le_mul_iff_left₀ wp).mp
      calc (τ*weight l)*weight l = τ*(weight l^2) := by ring
           _ ≤ τ*(major l*kernel l) := mul_le_mul_of_nonneg_left relation hτ.le
           _ ≤ kernel l*weight l := by
             have h:=mul_le_mul_of_nonneg_right (le_of_not_ge heavy) kp
             linarith only [h]
    have ew := mul_le_mul small ((le_div_iff₀ hτ).mpr (by simpa [mul_comm] using fine))
      wp.le hε
    have funded:=mul_nonneg hτ.le (mul_nonneg ed hp)
    apply ew.trans
    rw [show ε*(kernel l/τ)=(ε/τ)*kernel l by ring]
    exact le_add_of_nonneg_left funded
  have total:=shiny q share
  rw [pockets,sheen,sheen] at total
  exact total.trans (add_le_add (mul_le_mul_of_nonneg_left bank hτ.le)
    (mul_le_mul_of_nonneg_left geometry (div_nonneg hε hτ.le)))

theorem product_word_cost (q:ℕ) (cost:σ→ℝ) :
    Yarn q (fun l=>(l.map cost).prod) = (∑ i,cost i)^q := by
  induction q with
  | zero=>simp [Yarn]
  | succ q ih=>
    rw [twilled]
    simp only [List.map_cons,List.prod_cons,sheen,ih]
    rw [pow_succ',Finset.sum_mul]

end YM.Integration.FVA1Physical.Round2.Curvature
