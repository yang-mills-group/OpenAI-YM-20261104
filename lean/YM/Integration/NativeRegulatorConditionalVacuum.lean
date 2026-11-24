import YM.Integration.NativeWilsonCensusTrial
import YM.RG01.Kernel.Ratio

/-! Exact transverse angular response of the genuine finite conditional density on the funded family. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorConditionalVacuum

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators


open RG01 MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Price
variable {G : Gauge} (R : Run G) {N m p : ℕ} (hm : m < N)
  (V X : Config G (R.family.side m p)) (e : Edge (Site (R.family.side m p)) → ℝ)
local notation "H" => R.family.path
local notation "D" => ((H).rep N p m)
local notation "Step" => (H).levels.clock.op m p
local notation "β" => (H).β N p (m+1)
local notation "weight" => Kernel.expense H N m p V
local notation "source" => Kernel.channel Step β e V
local notation "sampled" => Kernel.encoded e V X

/-- The price uses only the actual weighted directions and the normalized
coarse displacement on those links. -/
def cost (R : Run G) (N m p : ℕ) (V X : Config G (R.family.side m p))
    (e : Edge (Site (R.family.side m p)) → ℝ) : ℝ :=
  |R.family.path.β N p (m+1) * (R.family.path.levels.clock.op m p).kernel.penalty| *
    Kernel.tariff G * (∑ i, e i) * ‖Kernel.encoded e V X‖

include hm

theorem relative (hs : ∀ i, e i=0 → X i=V i) :
    Kernel.generating weight source (Wilson.prior G (R.family.side (m+1) p)) 1 sampled =
      (↑((D).eval X) : ℂ) / (↑((D).eval V) : ℂ) := by
  have h := Kernel.trade H R.makes.wilson V hm (1:_) e X hs
  simpa only [Kernel.conditional,(Kernel.actual N H R.makes.wilson X hm).unit,mul_one] using h

theorem envelope (he : ∀ i, 0 ≤ e i) (hs : ∀ i, e i=0 → X i=V i) :
    ‖(↑((D).eval X) : ℂ) / (↑((D).eval V) : ℂ)‖ ≤ Real.exp (cost R N m p V X e) := by
  let μ := Wilson.prior G (R.family.side (m+1) p)
  let K := |β*(Step).kernel.penalty| * Kernel.tariff G * (∑ i, e i)
  have hp := Kernel.booked Step β e V ((H).levels.blocks m p).branches he
  have hc := Kernel.actual N H R.makes.wilson V hm
  have hu : Kernel.Bounded μ (1 : (Step).Choices → Config G (R.family.side (m+1) p) → ℂ) 1 :=
    ⟨fun _ => aestronglyMeasurable_const,fun _ _ => le_of_eq norm_one⟩
  have ht := hp.tilt_charge hu sampled (K*‖sampled‖) (mul_nonneg hp.sign (norm_nonneg _))
    (fun i x => ((source i x).le_opNorm sampled).trans
      (mul_le_mul_of_nonneg_right (hp.uniform i x) (norm_nonneg _))) zero_le_one
  rw [← relative R hm V X e hs]
  unfold Kernel.generating cost
  simpa only [K,one_mul] using hc.price ht

omit hm in
private theorem real_log {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ‖(a:ℂ)/(b:ℂ)‖ ≤ Real.exp q) : Real.log a - Real.log b ≤ q := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg ha.le,Complex.norm_real,
    Real.norm_of_nonneg hb.le] at h
  rw [← Real.log_div ha.ne' hb.ne']
  exact (Real.log_le_iff_le_exp (div_pos ha hb)).mpr h

/-- Bidirectional comparison on the same original fine Haar prior and all
the true conditional sector choices. -/
theorem absolute (he : ∀ i, 0 ≤ e i) (hs : ∀ i, e i=0 → X i=V i) :
    |Real.log ((D).eval X) - Real.log ((D).eval V)| ≤
      max (cost R N m p V X e) (cost R N m p X V e) := by
  have hX := Extra.Histories.Tour.bright H R.makes.wilson N p m hm.le X
  have hV := Extra.Histories.Tour.bright H R.makes.wilson N p m hm.le V
  have hf := real_log hX hV (envelope R hm V X e he hs)
  have hb := real_log hV hX (envelope R hm X V e he (fun i h => (hs i h).symm))
  exact abs_le.mpr ⟨by linarith only [hb,le_max_right (cost R N m p V X e) (cost R N m p X V e)],
    hf.trans (le_max_left _ _)⟩
end Price

variable {G : Gauge} {R : Run G} {hG : G.Simple} {W : Bank R hG} {μ : ℝ}
  {P : MS.Land.Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
  (T : Trial W μ P Z C A g i S)

local notation "𝓑" => C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)
local notation "periodSystem" => Period.Field.LodgeT.instance_real (program R) Z R C
  (schedule Z C T.order) (above Z C T.order)
local notation "𝓛" => Calibration.sheet T.calibrate
local notation "σ" => T.stop T.station

variable {n : ℕ} (v : Pegs.Motor (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)) n T.station)
  (d : Fin n → ℕ) (u : (a : Fin n) → (R.family.labels.level (d a)).Index)
local notation "𝓐" => T.stamp.traces T.station n σ v d u
local notation "𝓕" => Figure.prop R (ProgramT.spend (program R) Z R C
  (schedule Z C T.order) (above Z C T.order) T.location T.station n v) d u
variable (j : ℕ) (x : fieldDir G (R.family.side (NativeRegulatorInitialDatum.level T j) (T.stop T.station)) 1)
local notation "step₀" => NativeRegulatorInitialDatum.first T j
local notation "Y₁" => (periodSystem).records (𝓑).desk R.family.path σ (step₀).next
local notation "L₁" => T.stamp.menu.cloth (step₀).next
local notation:max "data₀" a:max => NativeRegulatorInitialDatum.datum T v d u j a
open Comparison.RG02.Moving.Path


open Comparison.RG02.Laplace
local notation "Y" => RunFormalChain.fromRun R
local notation "m₀" => NativeRegulatorInitialDatum.level T j
local notation "Δ₀" => R.family.path.levels.clock.op m₀ σ
local notation "V₁" => R.family.path.rep (m₀+1) σ m₀
local notation "τ₀" => Pert.Asymptotics.regulatorRun R.family (m₀+1) σ (m₀+1)
local notation:max "prime₁" y:max => See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := (step₀).next) y
local notation:max "visible₁" q:max y:max => See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) q y


local notation "τ" => NativeWilsonCensusTrial.coupling T j
local notation "X₀" => Integral.sample τ x
local notation "H₀" => R.family.path

/-- The physical logarithm at the moving coupling is represented by an
original signed angular generating function with the Wilson denominator
from this very regulator and field. -/
theorem measured (e : Edge (Site (R.family.side m₀ σ)) → ℝ) (hs : ∀ i, e i = 0 → (X₀) i=1) :
    Complex.exp (NativeRegulatorWilsonExpansion.logarithm T j x τ) =
      Kernel.generating (Kernel.expense H₀ (m₀+1) m₀ σ 1)
        (Kernel.channel Δ₀ ((H₀).β (m₀+1) σ (m₀+1)) e 1) (Wilson.prior G (R.family.side (m₀+1) σ))
        1 (Kernel.encoded e 1 X₀) := by
  have hl : NativeRegulatorWilsonExpansion.logarithm T j x τ =
      Complex.ofReal (Real.log ((V₁).eval X₀)) - Complex.ofReal (Real.log ((V₁).eval 1)) :=
    NativeRegulatorWilsonExpansion.logarithm_at T j x
  rw [relative R (Nat.lt_succ_self m₀) 1 X₀ e hs,hl,
    Complex.exp_sub, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  rw [Real.exp_log (Extra.Histories.Tour.bright H₀ R.makes.wilson _ _ _ (Nat.le_succ m₀) X₀),
    Real.exp_log (Extra.Histories.Tour.bright H₀ R.makes.wilson _ _ _ (Nat.le_succ m₀) 1)]

theorem physical_bound (e : Edge (Site (R.family.side m₀ σ)) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hs : ∀ i, e i=0 → (X₀) i=1) :
    ‖NativeRegulatorWilsonExpansion.logarithm T j x τ‖ ≤
      max (cost R (m₀+1) m₀ σ 1 X₀ e) (cost R (m₀+1) m₀ σ X₀ 1 e) := by
  have hl : NativeRegulatorWilsonExpansion.logarithm T j x τ =
      Complex.ofReal (Real.log ((V₁).eval X₀)) - Complex.ofReal (Real.log ((V₁).eval 1)) :=
    NativeRegulatorWilsonExpansion.logarithm_at T j x
  rw [hl,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact absolute R (Nat.lt_succ_self m₀) 1 X₀ e he hs

end YM.Integration.NativeRegulatorConditionalVacuum
end
