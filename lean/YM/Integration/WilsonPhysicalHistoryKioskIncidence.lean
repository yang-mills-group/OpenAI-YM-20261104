import YM.Integration.WilsonPhysicalHistoryKioskSalary
import YM.QuadraticLocal.Kiosk
import YM.QuadraticLocal.Pry

/-! The original expense of the second merger pays for the whole hot collar
in the shrunken output marker weights, uniformly over its genuine radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskIncidence
open Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal QuadraticLocal.Shelter
open scoped Classical BigOperators

theorem collar {n : Side} (H : ℕ) (x : Site n) :
    (Animals.neighbors (H+H) x).card ≤ 16*Animals.ballCost H := by
  refine (Animals.neighbors_card (H+H) x).trans ?_
  dsimp only [Animals.ballCost]
  calc
    _ ≤ (2*(H+H+1))^4 := Nat.pow_le_pow_left (by omega) 4
    _ = _ := by ring

theorem limit {G : Gauge} {n : Side} {p : BudgetPoint} {X Y : Activities G n}
    {e f a s : ℝ} (second : Kiosk.Second p X Y e f a s) : s ≤ 1 := by
  obtain ⟨fees,_,_,paid⟩ := second.softPaid.funds
  have original := paid (0:Site n)
  have nonnegative : 0 ≤ second.mainly := (tsum_nonneg original.1).trans original.2.2
  linarith [second.funds.soft_limit]

variable {V I I₁ I₀ T : Type*} [DecidableEq V] {G : Gauge} {n : Side} {p : BudgetPoint}
  {Z : Census V} {o : V → Site n} {w : V → ℝ} {B H : ℕ}
  (raw : Lamps T I G p o Z) (filed : Lamps T I₁ G p o Z) (residual : Lamps T I₀ G p o Z)
  (pos : ∀ v, 0<w v) {A b b₁ b₀ a τ radius : ℝ} (expo : 0≤A)
  (rawPaid : raw.Paid w B A b) (filedPaid : filed.Paid w B A b₁)
  (residualPaid : residual.Paid w B A b₀)

include pos expo rawPaid filedPaid residualPaid in
theorem funded (s : Z.Mode) (v : V) (live : v∈s.val) (t : T) (U : Config G n)
    (wide : 1≤radius) (weight : 0≤a*τ)
    (afford : radius⁻¹ * (Deck.crewCost H a τ*(b+b₁+b₀)) ≤ 1) :
    let value := Poly.toll (Stoop.radius w radius) s *
      ‖(raw.log t U-filed.log t U-residual.log t U).part s‖
    value * (Animals.ballCost H:ℝ) ≤ Real.exp (-A*(coverNumber B (s.val.image o) : ℝ)) ∧
    value * ((Animals.neighbors (H+H) (o v)).card:ℝ) ≤
      16*Real.exp (-A*(coverNumber B (s.val.image o) : ℝ)) := by
  intro value
  let spatial := Real.exp (-A*(coverNumber B (s.val.image o) : ℝ))
  let outcome := ‖(raw.log t U-filed.log t U-residual.log t U).part s‖
  let fee := b+b₁+b₀
  have expense := WilsonPhysicalHistoryKioskSalary.signed raw filed residual pos expo
    rawPaid filedPaid residualPaid s v live t U
  change _*outcome ≤ spatial*fee at expense
  have si : 0<spatial := Real.exp_pos _
  have hn : 0≤outcome := norm_nonneg _
  have hf : 0≤fee := by
    have := (mul_nonneg (Poly.worth pos s).le hn).trans expense
    exact nonneg_of_mul_nonneg_right this si
  have active : s≠Z.quiet := by
    intro clear
    rw [clear] at live
    exact notMem_empty v live
  have hr : 0<radius := zero_lt_one.trans_le wide
  have reduced := Stoop.shrink w s active pos wide
  have cap : radius⁻¹*((Animals.ballCost H:ℝ)*fee) ≤ 1 := by
    apply le_trans _ afford
    dsimp only [Deck.crewCost]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
    apply mul_le_mul_of_nonneg_right _ hf
    exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp_iff.mpr weight)
  have first : value*(Animals.ballCost H:ℝ) ≤ spatial := by
    change (Poly.toll (Stoop.radius w radius) s*outcome)*(Animals.ballCost H:ℝ) ≤ _
    calc
      _ ≤ ((radius⁻¹*Poly.toll w s)*outcome)*(Animals.ballCost H:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right reduced hn) (by positivity)
      _ = (radius⁻¹*(Animals.ballCost H:ℝ))*(Poly.toll w s*outcome) := by ring
      _ ≤ (radius⁻¹*(Animals.ballCost H:ℝ))*(spatial*fee) :=
        mul_le_mul_of_nonneg_left expense (by positivity)
      _ = spatial*(radius⁻¹*((Animals.ballCost H:ℝ)*fee)) := by ring
      _ ≤ spatial := mul_le_of_le_one_right si.le cap
  refine ⟨first,?_⟩
  have positive : 0 ≤ value := mul_nonneg (Poly.worth (fun z=>div_pos (pos z) hr) s).le hn
  have count : ((Animals.neighbors (H+H) (o v)).card:ℝ) ≤ 16*(Animals.ballCost H:ℝ) := by
    exact_mod_cast collar H (o v)
  calc
    _ ≤ value*(16*(Animals.ballCost H:ℝ)) := mul_le_mul_of_nonneg_left count positive
    _ = 16*(value*(Animals.ballCost H:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left first (by norm_num)

end YM.Integration.WilsonPhysicalHistoryKioskIncidence
end
