import YM.Integration.WilsonAddressedQuietAbsolute
import YM.Integration.WilsonAddressedPositiveRead
import YM.Integration.WilsonReceivedQuietCrownFlat
import YM.Integration.WilsonReceivedWholeFieldMask
import YM.Integration.WilsonFirstReceivedGalleryRegular

/-! Quantitative far peers in the genuine two-block mask subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedQuietPeer
open MeasureTheory Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants
open WilsonReceivedQuietCrownOwner WilsonCapturedPrimarySoftPartition WilsonFullFaceSignedMasks
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open PhysicalNext PhysicalNext.Repeat Further.PhysicalPeriodLimitF933
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open Primitives.GCC.Anchor WilsonThermometerEarlierWallet
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Countable ι] {J : Census V}
  {o : V→Site n} {P : Rep G n} (L : Lamps X ι G P.p o J)

def covered (q : (parts J).Mode) (x : X) (U : Config G n) := ∏t∈q.val,(L.log x U).part t.val
def declared (q : (parts J).Mode) (x : X) (U : Config G n) := ∏t∈q.val,(bare L x U).part t.val
def wage (w : V→ℝ) (C : ℝ) (q : (parts J).Mode) := ∏t∈q.val,C/Poly.toll w t.val

theorem filed (q : (parts J).Mode) (x : X) {w : V→ℝ} (wp : ∀v,0<w v)
    {a C D : ℝ} (ap : 0≤a) (paid : L.Paid w P.p.B a C) (gross : Gross L w P.p.B a D) :
    Measurable (covered L q x) ∧ Measurable (declared L q x) ∧
    (∀U, ‖covered L q x U‖ ≤ wage w C q) ∧ (∀U, ‖declared L q x U‖ ≤ wage w D q) := by
  have h (s : J.Mode) : Measurable (fun U => (L.log x U).part s) := by
    apply (Poly.get s).continuous.measurable.comp
    apply Measurable.tsum (f:=fun i U => L.frame i x U)
    intro i
    apply (Overlay.Bands.sends _).measurable.comp
    unfold Lamps.light
    split
    · exact (L.legal x i).borel
    · exact masked_measurable _ _ _ (L.legal x i).borel
  refine ⟨Finset.measurable_prod _ (fun t _=>h t.val),
    Finset.measurable_prod _ (fun t _=>WilsonReceivedWholeFieldMask.measurable L wp ap gross x t.val),?_,?_⟩
  · intro U
    rw [covered,norm_prod]
    apply prod_le_prod (fun _ _=>norm_nonneg _)
    intro t _
    obtain ⟨v,hv⟩:=t.property
    apply (le_div_iff₀ (Poly.worth wp _)).mpr
    simpa only [mul_comm] using WilsonFirstReceivedGalleryRegular.occupied L paid ap wp x U t.val v hv
  intro U
  rw [declared,norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro t _
  obtain ⟨v,hv⟩:=t.property
  apply (le_div_iff₀ (Poly.worth wp _)).mpr
  simpa only [mul_comm] using WilsonReceivedWholeFieldMask.whole L wp ap gross x U t.val v hv

variable (R : Run G) {N per m k b u : ℕ} (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin)
  (Ψ : ∀j, Rep G (R.family.side j per)) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (top : b ≤ N) {d : ℕ} {F : Frame G d} (S : SectionData F) (Y : Hol G)
  (simple : G.Simple) (way : WayStation R.kit)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (ticket : TicketP R.alloy R.kit D Q) (floor : m≤u) (ub : u≤b)
  (fixed : WilsonSingleHardRadius.first R simple≤u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Xb" => Config G (R.family.side b per)
local notation "W" => Ψ b

include way ticket course top floor ub fixed S Y in
theorem one (y : Site (R.family.side b per)) {c : ℝ} {slip peer : Xb→ℂ} {mass : ℝ}
    (sm : Measurable slip) (pm : Measurable peer) (pe : ∀U,‖peer U‖≤ mass)
    (B : Xb→ℝ) (cover : ∀U,‖slip U‖≤B U)
    (held : Owned (F:=F) (W) Y y κ c (fun U=>((W).eval U:ℂ)*(B U:ℂ)))
    (p : ℕ) {ε : ℝ} (ep : 0<ε) (late : WilsonSingleHardRadius.start R simple p ep≤b) :
    Admitted (u:=u) (N:=N) R (le_refl b) (fun U=>((W).eval U:ℂ)*slip U*peer U)
      (mass*(4*(1+|c|)*ε/β^p)) := by
  have pos := (norm_nonneg _).trans (pe (1:Xb))
  have earned := WilsonReceivedQuietCrownFlat.one R π Γ Ψ course top S Y y simple way D Q ticket floor ub fixed held p ep late
  have walk := course.1.walk b (floor.trans ub) top
  have vac U : 0≤(W).eval U := by
    have same : (W).eval = (R.family.path.rep N per b).eval := walk.view
    rw [congrFun same U]
    exact (Multi.AxisShift.chosen_positive R.makes.wilson top U).le
  let f := fun U => ((W).eval U:ℂ)*slip U*peer U
  let h := fun U => ((W).eval U:ℂ)*(B U:ℂ)
  have bounded U : ‖f U‖ ≤ mass*(h U).re := by
    simp only [f,h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (vac U),
      ←Complex.ofReal_mul,Complex.ofReal_re]
    calc
      (W).eval U*‖slip U‖*‖peer U‖ ≤ (W).eval U*B U*mass :=
        mul_le_mul (mul_le_mul_of_nonneg_left (cover U) (vac U)) (pe U) (norm_nonneg _) (mul_nonneg (vac U) ((norm_nonneg _).trans (cover U)))
      _ = mass*((W).eval U*B U) := mul_comm _ _
  have test : Measurable f :=
    ((Complex.continuous_ofReal.measurable.comp ((W).envelope walk.truep.valid).meas).mul sm).mul pm
  refine ⟨(earned.1.norm.const_mul mass).mono' test.aestronglyMeasurable (ae_of_all _ (fun U=>?_)),?_⟩
  · exact (bounded U).trans (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) pos)
  intro a ua ab
  exact (WilsonAddressedPositiveRead.original R f h earned.1 pos bounded ab).trans
    (mul_le_mul_of_nonneg_left (earned.2 a ua ab) pos)

end YM.Integration.WilsonAddressedQuietPeer
