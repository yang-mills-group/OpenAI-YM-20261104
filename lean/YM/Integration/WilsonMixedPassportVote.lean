import YM.Integration.WilsonMixedFaceLog
import YM.Integration.WilsonOriginalCompensatedPortfolio

/-! The second voter on independent old and fresh positions, using the two actual face salaries. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedPassportVote
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn WilsonMixedPassportRows WilsonMixedPassportArmada
open Finset RG Marker Lattice QuadraticLocal QuadraticLocal.Earn PhysicalNext PhysicalNext.Repeat Push Push.AbsoluteSums Push.PriceCompiler
open Next.Scheduling
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V α β γ ι κ : Type} [DecidableEq V] {C : Census V}
  {P Q : Passport n V} (M : ι → Row P C G α) (Y : κ → Row Q C G β)
  (old fresh : Finset V) (sep : Disjoint old fresh) (leftTest : γ → α) (rightTest : γ → β)

def choice {A : Type} (old : Finset V) (x y : V → A) (v : V) : A := if v ∈ old then x v else y v

private theorem facePrice (p : V → Passport n V) (home : ∀ v ∈ old, p v = P)
    (w w' : V → ℝ) (t t' : V → ℕ) {s c : ℝ} {o d e o' d' e' : ℕ}
    (input : Scene.Armada M w t s c o d e) (more : o ≤ o') (room : Scene.Ministry C t' d' e')
    (positive : ∀ v, 0 < w' v) (cash : ∀ v ∈ old, w' v = w v) (mode : ∀ v ∈ old, t' v = t v) :
    Scene.Armada (roster M old p home leftTest) w' t' s c o' d' e' := by
  let X := roster M old p home leftTest
  have received := WilsonMixedPassportArmada.original M old p home leftTest w t t input input.toMinistry (fun _ _ => rfl)
  refine ⟨room, positive, ?_, ⟨received.purchases.spend, ?_⟩, received.honor⟩
  · intro y
    have weights (i : Face M old) : Poly.toll w' (X i).mode = Poly.toll w (X i).mode :=
      Finset.prod_congr rfl (fun v hv => cash v (i.property hv))
    change SumBudget (fun i => if (X i).center=y then Poly.toll w' (X i).mode * (X i).height s else 0) c
    simp only [weights]
    exact received.suggests y
  · intro i
    obtain ⟨low, invoice⟩ := received.purchases.usable i
    exact ⟨low.trans more, invoice.trans (Finset.sum_congr rfl (fun v hv => (mode v (i.property hv)).symm))⟩

def gradeTotal [Fintype V] (old : Finset V) (a b : V → ℕ) := ∑ v, choice old a b v

local notation "S" => WilsonMixedFaceLog.routed M Y old fresh sep leftTest rightTest

theorem original [Fintype V] {w₀ w₁ : V → ℝ} {t₀ t₁ : V → ℕ} {s f g Ω : ℝ}
    {o₀ d₀ e₀ o₁ d₁ e₁ fine coarse vac : ℕ}
    (school : Syl.School vac) (step : StepStages fine coarse) (enough : AllOrder.Burn.horizon vac+2 ≤ coarse)
    (input : Scene.Armada M w₀ t₀ s f o₀ d₀ e₀) (birth : Scene.Armada Y w₁ t₁ s g o₁ d₁ e₁)
    (oldOrder : o₀ ≤ school.order) (freshOrder : o₁ ≤ school.order) (arity : Fintype.card V ≤ school.pieces)
    (degree : gradeTotal old t₀ t₁ ≤ school.horizon) (paidOld : f ≤ Ω⁻¹) (paidFresh : g ≤ Ω⁻¹) :
    Scene.Armada S (Stoop.radius (choice old w₀ w₁) 2) (choice old t₀ t₁) s ((2:ℝ)⁻¹*(f+g))
      school.order school.pieces school.horizon ∧ (2:ℝ)⁻¹*(f+g) ≤ Ω⁻¹ ∧
    Mentor.Cruise.Voter S s school.order (school.room step enough).count (school.room step enough).stage vac coarse := by
  let w := choice old w₀ w₁
  let t := choice old t₀ t₁
  have pos (v : V) : 0 < w v := by
    change 0 < (if v ∈ old then w₀ v else w₁ v)
    split <;> first | exact input.positive v | exact birth.positive v
  have room : Scene.Ministry C t school.pieces school.horizon := by
    refine ⟨fun v => v.val.card_le_univ.trans arity, fun v => ?_⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ v.val) (fun j _ _ => Nat.zero_le (t j))).trans degree
  let p := owner P Q old
  have left (v : V) (hv : v ∈ old) : p v = P := if_pos hv
  have absent (v : V) (hv : v ∈ fresh) : v ∉ old := fun h => Finset.disjoint_left.mp sep h hv
  have right (v : V) (hv : v ∈ fresh) : p v = Q := if_neg (absent v hv)
  have A := facePrice M old leftTest p left w₀ w t₀ t input oldOrder room pos
    (fun _ h => if_pos h) (fun _ h => if_pos h)
  have B := facePrice Y fresh rightTest p right w₁ w t₁ t birth freshOrder room pos
    (fun v h => if_neg (absent v h)) (fun v h => if_neg (absent v h))
  exact WilsonOriginalCompensatedPortfolio.voters (roster M old p left leftTest)
    (roster Y fresh p right rightTest) school step enough A B paidOld paidFresh

end YM.Integration.WilsonMixedPassportVote
