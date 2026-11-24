import YM.Integration.WilsonMixedPassportArmada
import YM.Integration.WilsonMixedTestTableau
import YM.Integration.WilsonRootedKioskOccupiedSlip
import YM.QuadraticLocal.Class.Spill

/-! The independently enrolled new rows at their own date in an old and fresh
wallet. The full-group bound is taken before the original healthy masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRightBirthLamp
open Function Finset Lattice Wilson RG Marker Ac Push Push.AbsoluteSums
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity WilsonMixedPassportRows
open scoped Classical BigOperators
variable {G : Gauge} {V I : Type} [DecidableEq V] {n : Side} {C : Census V}
  {P Q : Passport n V} {E F : V → Type}
  [∀ i, AddCommGroup (E i)] [∀ i, AddCommGroup (F i)]
  [∀ i, Module ℝ (E i)] [∀ i, Module ℝ (F i)]
  (A : ∀ i, Set (E i)) (B : ∀ i, Set (F i))
  (K : ∀ i, Submodule ℝ (E i)) (L : ∀ i, Submodule ℝ (F i))
  (Y : I → Row Q C G (Wallet B))
  (P : Passport n V) (old fresh : Finset V) (apart : Disjoint old fresh) (zero : ∀ i, 0 ∈ B i)

def rows := WilsonMixedPassportArmada.roster Y fresh (owner P Q old)
  (fun _ h => if_neg (fun hold => Finset.disjoint_left.mp apart hold h))
  (WilsonMixedTestTableau.right A B fresh zero)

local notation "X" => rows A B Y P old fresh apart zero
local notation "right" => WilsonMixedTestTableau.right A B fresh zero
local notation "Fees" => Scene.Armada
open private transport from YM.Integration.WilsonMixedTestTableau

theorem tested (file : Tableau L B Y) :
    Tableau (WilsonMixedTestTableau.pieces K L) (WilsonMixedTestTableau.actors A B) X := by
  constructor
  intro i
  apply transport (file.bill i.val) (WilsonMixedTestTableau.rightAt A B fresh zero)
  · intro j hj x y z c d eq
    simp only [WilsonMixedTestTableau.rightAt, if_pos (i.property hj)]
    exact congrArg Prod.snd eq
  · intro j hj t nil
    simp only [WilsonMixedTestTableau.rightAt, if_pos (i.property hj)]
    exact nil.2

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, Module ℝ (F i)] in
theorem tariff {w u : V → ℝ} {t : V → ℕ} {σ cost : ℝ} {j k h : ℕ}
    (income : Fees Y w t σ cost j k h) (positive : ∀ i, 0 < u i) (fits : ∀ i ∈ fresh, u i ≤ w i) :
    Fees X u t σ cost j k h := by
  have receipt : Fees X w t σ cost j k h := WilsonMixedPassportArmada.original
    Y fresh (owner P Q old) (fun _ hi => if_neg (fun ho => Finset.disjoint_left.mp apart ho hi))
    right w t t income income.toMinistry (fun _ _ => rfl)
  refine ⟨receipt.toMinistry,positive,?_,receipt.purchases,receipt.honor⟩
  intro x
  apply budget_mono (receipt.suggests x)
  · intro i
    split
    · exact mul_nonneg (Finset.prod_nonneg fun a _ => (positive a).le) (mul_nonneg (X i).sound.le (Real.exp_pos _).le)
    · exact le_rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right
        (Finset.prod_le_prod (fun a _ => (positive a).le) (fun a ha => fits a (i.property ha))) (mul_nonneg (X i).sound.le (Real.exp_pos _).le)
    · exact le_rfl

section full
variable {T : Type} {J : Passport n V} (Z : I → Row J C G T)
theorem gross (point : BudgetPoint) {g x s a θ σ c : ℝ} {j k h : ℕ} {w : V → ℝ} {t : V → ℕ}
    (fee : Fees Z w t σ c j k h) (invoice : Invoice.Supports point x s g σ θ) (narrow : a ≤ s) :
    WilsonRootedKioskOccupiedSlip.Gross (rendered Z point g) w point.B a
      (Spill.allOver point ^ (j+h+1) * (Invoice.price point x (j+h+1) k s θ G * c)) := by
  let H := Spill.allOver point ^ (j+h+1)
  have hH : 0 ≤ H := pow_nonneg (zero_le_one.trans (Spill.allOver_ge point)) _
  have nonnegative (i:I) : 0 ≤ (Z i).charge point g :=
    mul_nonneg (mul_nonneg (by positivity) ((Z i).real_quote point g).1) (Z i).sound.le
  refine ⟨fun i => H * (Z i).charge point g,fun i => mul_nonneg hH (nonnegative i),?_,?_⟩
  · intro i t₀ U
    exact Spill.nominal_price point g _ t₀ _ (fee.honor i) (Scene.Armada.degreeR t fee.toMinistry _ (fee.purchases.usable i)).2.2 U
  · intro y
    apply budget_mono (budget_scale hH (Scene.Armada.hits Z w t fee point invoice y))
    · intro i
      change 0 ≤ if y ∈ (Z i).ground point then _ else _
      split
      · exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun v _ => (fee.positive v).le))
          (mul_nonneg hH (nonnegative i))) (Real.exp_pos _).le
      · exact le_rfl
    · intro i
      change (if y ∈ (Z i).ground point then _ else _) ≤ H * (if y ∈ (Z i).ground point then _ else _)
      split
      · unfold Invoice.income
        have ht : 0 ≤ Poly.toll w (Z i).mode := Finset.prod_nonneg (fun v _ => (fee.positive v).le)
        have hc : 0 ≤ (coverNumber point.B ((Z i).ground point) : ℝ) := by positivity
        change Poly.toll w (Z i).mode * (H * (Z i).charge point g) * Real.exp _ ≤ _
        rw [show Poly.toll w (Z i).mode * (H * (Z i).charge point g) = H * (Poly.toll w (Z i).mode * (Z i).charge point g) by ring, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right narrow hc)) (mul_nonneg ht (nonnegative i))) hH
      · rw [mul_zero]
end full

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, Module ℝ (F i)] in
theorem unmaskedSum (point : BudgetPoint) (g : ℝ)
    (x : Wallet (WilsonMixedTestTableau.actors A B)) (U : Config G n) :
    WilsonRootedKioskOccupiedSlip.bare (rendered X point g) x U =
      ∑' i : Face Y fresh, Poly.send (Y i.val).mode ((Y i.val).nominal g (right x) U) := by
  unfold WilsonRootedKioskOccupiedSlip.bare
  apply tsum_congr
  intro i
  have same := WilsonMixedPassportRows.original (owner P Q old) (Y i.val)
    (fun _ hv => if_neg (fun ho => Finset.disjoint_left.mp apart ho (i.property hv)))
    right point g x
  exact congrArg (Poly.send (Y i.val).mode) (congr_fun same.2.2.2 U)

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] in
theorem unmasked (file : Tableau L B Y) [Fintype I] (point : BudgetPoint) (g : ℝ)
    (x : Wallet (WilsonMixedTestTableau.actors A B)) (U : Config G n) :
    WilsonRootedKioskOccupiedSlip.bare (rendered X point g) x U =
      ∑ i,Poly.send (Y i).mode ((Y i).nominal g (right x) U) := by
  rw [unmaskedSum]
  let f (i:I) : Poly C := Poly.send (Y i).mode ((Y i).nominal g (right x) U)
  have live : Function.support f ⊆ {i | (Y i).mode.val ⊆ fresh} := by
    intro i hi v hv
    by_contra absent
    have dead := (file.bill i).idle v hv (right x) (by
      change (WilsonMixedTestTableau.rightAt A B fresh zero v (x v)).val ∈ L v
      simp only [WilsonMixedTestTableau.rightAt,if_neg absent]
      exact (L v).zero_mem)
    apply hi
    change Poly.send (Y i).mode ((Y i).paint (right x) * _) = 0
    rw [dead,zero_mul,Poly.send_zero]
  exact ((hasSum_subtype_iff_of_support_subset live).mpr (hasSum_fintype f)).tsum_eq

end YM.Integration.WilsonOriginalRightBirthLamp
