import YM.Integration.WilsonOriginalPublicNodalCommonRaw
import YM.Integration.WilsonIndependentPublicReportComplex

/-! A comparison of the two held programmes through their common integrated
bare Wilson word, with the actual two reporting clocks.  Both spatial error
bills are charged after the normalized thermal substitution. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkCommonRawClocks
open WilsonOriginalPublicNodalCommonRaw (Court Offered fee prior raw value)
open WilsonOriginalPublicNodalSafeCenter (moved)
open WilsonIndependentPublicReportComplex (row)
open WilsonIndependentPublicReportClock WilsonIndependentPublicReportBias
open PowerSeries RegulatorIR RegulatorIR.Binding RegulatorIR.Profiles RegulatorIR.Clocks
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Motion
open WilsonIndependentRawRosterOrbit (report)
open WilsonIndependentRawRosterWord (film)
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalSafeCenter (moved)
open XSpace XSpace.Cirrus WilsonCoeffUV
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Motion
open scoped Classical ENNReal NNReal BigOperators PowerSeries

def heard (K : Feeds) (pole q : ℕ) (f : ℕ → ℂ) : ℂ :=
  coeff q (WilsonIndependentPublicReportComplex.apply K pole (PowerSeries.mk f))

def bill (K : Feeds) (pole q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (q+1), f j * |row K pole q j|

theorem on_film (K : Feeds) (pole q : ℕ) (f b : ℕ → ℂ) (income : ℕ → ℝ)
    (near : ∀ j ≤ q, ‖f j-b j‖ ≤ income j) :
    ‖heard K pole q f - heard K pole q b‖ ≤ bill K pole q income := by
  unfold heard bill
  rw [WilsonIndependentPublicReportComplex.difference]
  simp only [coeff_mk]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (near i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (abs_nonneg _)

variable {G : Gauge} {X I : Type} {p : ℕ}
variable (R : PhysicalNext.Repeat.Legato.Run G) (W : Initialize G) (sign : I → Bool) (d : I → ℕ)
    (key : ∀ i, (R.family.labels.level (d i)).Index) (arms : Composite I)

theorem original (A B : Court G X p) (sample : X → Sample 2) (sites : X → I → Cover)
    (center : X → Room) (c₁ c₂ : ℝ) (left : Offered arms A sample sites center c₁)
    (right : Offered arms B sample sites center c₂)
    (j : Choice A.M) (k : Choice B.M) (olderA : A.D.age ≤ j.age) (olderB : B.D.age ≤ k.age)
    (s t : X → Cover) :
    ∃ a b c : ℕ → ℝ, ∃ α β γ : ℕ → ℕ,
      ∀ q ≤ p, ∀ (n : Page k.after.spans) (K₁ K₂ : Feeds) (h₁ h₂ : ℕ),
        let w := n.bindW
        let f := value R W sign d key arms A (moved A.V j s sites) (j.choose w)
        let b₀ := raw R W sign d key arms (sample w) (sites w)
        let h := value R W sign d key arms B (moved B.V k t sites) (k.after.page n)
        ‖(heard K₁ h₁ q f-heard K₂ h₂ q h) - (heard K₁ h₁ q b₀-heard K₂ h₂ q b₀)‖ ≤
          bill K₁ h₁ q (fun l => fee A (a l) (α l) j w) +
          bill K₂ h₂ q (fun l => fee B (b l) (β l) k w + prior B (c l) (γ l) k w) := by
  choose a b c α β γ _ha _hb _hc price using fun l : ℕ =>
    WilsonOriginalPublicNodalCommonRaw.intersection R W sign d key arms A B sample sites center c₁ c₂
      left right j k olderA olderB s t (min l p) (Nat.min_le_right l p)
  refine ⟨a,b,c,α,β,γ,?_⟩
  intro q hq n K₁ K₂ h₁ h₂ w f b₀ h
  have bounds (l : ℕ) (hl : l ≤ q) :
      ‖f l-b₀ l‖ ≤ fee A (a l) (α l) j w ∧
      ‖b₀ l-h l‖ ≤ fee B (b l) (β l) k w + prior B (c l) (γ l) k w := by
    have res := price l n
    rw [Nat.min_eq_left (hl.trans hq)] at res
    exact ⟨res.1,res.2.1⟩
  rw [show (heard K₁ h₁ q f-heard K₂ h₂ q h)-(heard K₁ h₁ q b₀-heard K₂ h₂ q b₀)=
    (heard K₁ h₁ q f-heard K₁ h₁ q b₀)+(heard K₂ h₂ q b₀-heard K₂ h₂ q h) by ring]
  exact (norm_add_le _ _).trans (add_le_add (on_film K₁ h₁ q f b₀ _ fun l hl => (bounds l hl).1)
    (on_film K₂ h₂ q b₀ h _ fun l hl => (bounds l hl).2))

end YM.Integration.WilsonMovingForkCommonRawClocks
