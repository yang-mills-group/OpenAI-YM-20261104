import YM.Integration.WilsonOriginalTwoPrintPhysicalPrice

/-! The two physical print fees in terms of one chronological rooted income.
The restored income includes the entire mode wallet and every printed scalar.
The only explicit negative coupling power on the gross group word is its shelf. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPrintWallet
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums AllOrder AllOrder.Floe Laurent Comparison.Density
open Transport AnalyticBridge.SectorAffine.Offset
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {V A : Type} [Fintype A] [DecidableEq V] {Γ : Census V}

def restored (w : A→V→ℝ) (s : Γ.Mode) (c b : A→ℝ) (a : A) :=
  |c a| * (Poly.toll (w a) s)⁻¹ * b a

def jetRate (G : Gauge) (B : BudgetPoint) (J ℓ p pieces depth : ℕ) (θ : ℝ) :=
  WilsonEmittedTransitionJet.fee J ℓ (WilsonEmittedLocatedCensus.receipt G B J
    (p+depth+1) pieces 0 1 (B.supportExponent+2) θ)

def wordRate (B : BudgetPoint) (p pieces depth : ℕ) (θ : ℝ) :=
  2^(p+depth+1) * WilsonEmittedGroupWallet.stock B (p+depth+1) pieces 0 1 θ

variable (w : A→V→ℝ) (s : Γ.Mode) (c b θ : A→ℝ) (ℓ p pieces depth : A→ℕ)
variable (B : BudgetPoint) (J : ℕ)

theorem jets :
    WilsonEmittedFiledCatalogue.rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
        (b:=b) (α:=fun _ => B.supportExponent+2) (θ:=θ) s J 0 =
      ∑ a, restored w s c b a * jetRate G B J (ℓ a) (p a) (pieces a) (depth a) (θ a) := by
  unfold WilsonEmittedFiledCatalogue.rent
  apply sum_congr rfl; intro a _
  simp only [restored,jetRate,WilsonEmittedTransitionJet.fee,WilsonEmittedLocatedCensus.receipt,
    Footprint.payment,Footprint.degreeIncome,pow_zero,mul_one]
  ring

theorem word (g : ℝ) :
    WilsonEmittedLongInvoice.gross w c (fun _=>0) B s 0 g p pieces depth b θ =
      ∑ a, (restored w s c b a * wordRate B (p a) (pieces a) (depth a) (θ a)) *
        (g^(depth a+1))⁻¹ := by
  unfold WilsonEmittedLongInvoice.gross
  apply sum_congr rfl; intro a _
  simp only [restored,wordRate,WilsonEmittedLongInvoice.scalar,WilsonEmittedGroupWallet.ceiling,
    WilsonEmittedGroupWallet.stock,Footprint.payment,Footprint.degreeIncome,pow_zero,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  ring

theorem both (g : ℝ) (tube : LinkTube G) (d : ℕ) (I U : ℝ)
    (hg : 0 < g) (hg' : g ≤ 1) (hu : 0 ≤ U)
    (positive : ∀ a, 0 ≤ restored w s c b a) (income : ∑ a, restored w s c b a ≤ I)
    (shelf : ∀ a, depth a ≤ d)
    (jet : ∀ a, groupPrice tube 0 * jetRate G B J (ℓ a) (p a) (pieces a) (depth a) (θ a) ≤ U)
    (raw : ∀ a, wordRate B (p a) (pieces a) (depth a) (θ a) ≤ U) :
    groupPrice tube 0 * WilsonEmittedFiledCatalogue.rent (G:=G) w c ℓ B (p:=p)
          (pieces:=pieces) (depth:=depth) (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s J 0
          ≤ I * U ∧
    WilsonEmittedLongInvoice.gross w c (fun _=>0) B s 0 g p pieces depth b θ
          ≤ I * U * (g^(d+1))⁻¹ := by
  have bound : ∑ a, restored w s c b a * U ≤ I*U := by
    simpa only [sum_mul] using mul_le_mul_of_nonneg_right income hu
  constructor
  · rw [jets, mul_sum]
    apply le_trans (sum_le_sum ?_) bound
    intro a _
    simpa only [mul_left_comm, mul_assoc, mul_comm] using
      mul_le_mul_of_nonneg_left (jet a) (positive a)
  · rw [word]
    have limit := mul_le_mul_of_nonneg_right bound (inv_nonneg.mpr (pow_nonneg hg.le (d+1)))
    rw [sum_mul] at limit
    apply le_trans (sum_le_sum ?_) limit
    intro a _
    have dvd : (g^(depth a+1))⁻¹ ≤ (g^(d+1))⁻¹ := by
      apply (inv_le_inv₀ (pow_pos hg _) (pow_pos hg _)).2
      exact pow_le_pow_of_le_one hg.le hg' (Nat.succ_le_succ (shelf a))
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (raw a) (positive a))
      (by positivity)).trans (mul_le_mul_of_nonneg_left dvd (mul_nonneg (positive a) hu))

end YM.Integration.WilsonIndependentCollarPrintWallet
