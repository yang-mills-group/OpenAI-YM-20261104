import YM.Integration.WilsonCapturedPrimaryWindingBanks
import YM.Integration.WilsonEmittedFiledGerm

/-! The original census determines its mixed jets by discharging its actual rows.
The two-bank comparison only needs the finite time-one coefficients of that discharge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingCensusRead
open Function Finset Tensor Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.RG02.Adjacent Comparison.Density
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.FVAAlt2 RegulatorIR.Diagram
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open WilsonIndependentCapturedAngularWinding WilsonEmittedFiledThermalGerm
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w:A→V→ℝ) (grades:A→V→ℕ)
variable (x:(a:A)→X a) (c:A→ℝ) (ℓ:A→ℕ)
variable (B:BudgetPoint) {σ b α K θ:A→ℝ} {p pieces depth:A→ℕ} {g:ℝ}
variable (old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope:∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s:Multi.Hot Γ) (layout:A→Layout G) (tapes:A→Finset Age)
variable {L:Type} [DecidableEq L] {C:Census L}
local notation "full" => (fun z:Chart G n=>words M x c ℓ (fun a=>picked (M a) s.val) z.1 (increment 1 z.2))
local notation "board" => WilsonEmittedFiledMixedWindow.joint G n

theorem tested (F : Chart G n→ℂ) (H : ℝ×Stationary.Link G n→ℂ) (d:ℕ)
    (f : ContDiffAt ℝ d F 0) (h : ContDiffAt ℝ d H 0)
    (listened : ∀v:Directions G n, Assembly.jet F d (1,v)=Assembly.jet H d (1,Stationary.edgeColor.symm v)) :
    iteratedFDeriv ℝ d F 0 = iteratedFDeriv ℝ d (H ∘ board) 0 := by
  have h₀ : ContDiffAt ℝ d H (board 0) := by simpa only [map_zero] using h
  have h₁ := h₀.comp 0 (WilsonEmittedFiledMixedWindow.joint G n).contDiff.contDiffAt
  have eq := WilsonCapturedPrimaryWindingPeg.section_ext (Tensor.coeff F d 0)
    (Tensor.coeff (H ∘ board) d 0) (Tensor.coeff_symm f) (Tensor.coeff_symm h₁) (by
      intro v
      exact (listened v).trans (Assembly.jet_continuous_right board (f:=H) h₀ (1,v)).symm)
  have restore (T:Chart G n→ℂ) : (d.factorial:ℝ) • Tensor.coeff T d 0=iteratedFDeriv ℝ d T 0 := by
    simp [Tensor.coeff,smul_smul,Nat.factorial_ne_zero]
  rw [←restore F,eq,restore]

include old scope in
theorem original (V₁ V₂:Bulk.Colors C G n) (c₁ c₂:UnitCost) (u:L)
    (well₁:Bulk.Well V₁) (well₂:Bulk.Well V₂) (tables₁ tables₂:Orders (SiteSlot G n))
    {cap toll J:ℕ} (room:J≤cap+toll+1)
    (t₁:V₁.power (Booth.Arm.pub u)=toll) (t₂:V₂.power (Booth.Arm.pub u)=toll)
    (issued:Booth.Arm.Single c₁ V₁ tables₁ u cap toll) (scheduled:Booth.Arm.Single c₂ V₂ tables₂ u cap toll)
    (booked:∀d<J,∀v:Directions G n,
      (∑a,c a • WilsonEmittedFiledGerm.price M grades x ℓ s layout tapes d v a)=
        Assembly.jet (field c₁ V₁ u-field c₂ V₂ u) d (1,Stationary.edgeColor.symm v))
    {fee:ℝ} (fee0:0≤fee)
    (cash:∀e:ℕ,e+toll<J→
      ((e+toll).factorial:ℝ)*WilsonEmittedAngularJointFare.mass
        (fun r x=>((tables₁ e r x-tables₂ e r x:ℝ):ℂ)) (e+toll) ≤ fee) :
    ∀d<J, ∑i : Fin d→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ d full 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖ ≤ fee := by
  intro d hd
  have read := WilsonEmittedFiledGerm.heard M w grades x c ℓ B old scope s layout tapes d
  have analytic := WilsonEmittedFiledGerm.smooth M w grades x c ℓ B old scope s layout tapes
  have h := (WilsonEmittedFiledThermalGerm.smooth c₁ V₁ u well₁).sub
    (WilsonEmittedFiledThermalGerm.smooth c₂ V₂ u well₂)
  rw [tested full _ d (analytic.of_le le_top) (h.of_le le_top) (fun v=>(read v).trans (booked d hd v))]
  exact WilsonCapturedPrimaryWindingBanks.original V₁ V₂ c₁ c₂ u well₁ well₂ tables₁ tables₂
    room t₁ t₂ issued scheduled fee0 cash d hd

end YM.Integration.WilsonCapturedPrimaryWindingCensusRead
