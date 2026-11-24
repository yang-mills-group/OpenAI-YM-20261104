import YM.Integration.WilsonCapturedPrimaryPointBasis
import YM.Integration.WilsonOlderFreshPointChart
import YM.QuadraticLocal.Class.Foundry

/-! One actual published point roster and the finite nonaveraged chart that it records
at the binder's own site. Absolute-link directions can be chosen after publication. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointIncome
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada
open FormalBulk08 FormalBulk08.Pose FormalBulk08.Dawn Planned.PrimaryIntegral295 Exterior
open PhysicalNext.Repeat.Legato WilsonCapturedPrimaryPointBasis
open scoped Classical BigOperators Topology
variable {G : Gauge} {d D Q : ℕ} {σ : ℝ} (R : Run G) (L : Primer.Families R.family)
    (a : G.ColorIndex) (depth : d<D) (i : ℕ) (b : Letter (R.family.labels.level d))
    (p : WilsonOlderFreshPointGauge.Ballot R i D) (T : WilsonOlderFreshGraphSlate.Copy G d Q σ)
variable (posted : WilsonOlderFreshPointCommission.Published R L a depth i b p T)
variable {n : Side} {P : Earn.Passport n Unit} {H : Marker.Census Unit}
    (S : Earn.Binder P H) (E : Unit→Set ℂ) (t : Affinity.Wallet E)
local notation "M" => T.rows S E
local notation "f" => WilsonOlderFreshPointGauge.panel R L a depth i b p n (WilsonElectedPrimaryTensor.pin S.center)
include posted in
theorem original (cap : ∀ x, ‖value E x‖≤1) (σ₀ : 0<σ)
    (layout : Layout G) (stock : Finset Age) (e : ℕ) (he : e≤Q) (A : Link G n) :
    HasSum (fun z=>(M z).paint t * ((M z).markReceipt e A : ℂ))
      (value E t * (f e A : ℂ)) := by
  have salary := WilsonOriginalPrimerCourseRead.salary S T.roll T.fare σ T.paid T.legal T.positive E cap t σ₀
  have total := Air.basis M (fun z=>(M z).paint t) (fun _=>d) salary layout stock A (submitted S) e
  have booked := WilsonOriginalPrimerDischarge.filed S T.roll T.fare σ T.paid T.legal T.positive
    (value E) t σ₀ salary layout stock A e
  have named := posted ⟨e,Nat.lt_succ_of_le he⟩ n A (WilsonElectedPrimaryTensor.pin S.center)
  rw [named,←booked]
  refine total.congr_fun fun z=>?_
  rw [Poly.part_send, if_pos (show (submitted S).val=(M z).mode from rfl)]

/-- An absolutely convergent scalar reading of this one live binder is the complete
uncut source. Every term keeps the physical mode in the original census. -/
theorem uncut (g : ℝ) (U : Config G n) (total : ℂ)
    (posted : HasSum (fun z=>(M z).nominal g t U) total) :
    (Spill.Foundry.uncut M g t U).part S.mode = total := by
  have pushed := posted.smul_const (Poly.send S.mode (1:ℂ))
  have all : HasSum (fun z=>Spill.raw M g t z U) (total • Poly.send S.mode 1) := by
    refine pushed.congr_fun fun z=>?_
    apply YM.Marker.Poly.ext
    intro s
    change (Poly.send S.mode _).part s=(_ • Poly.send S.mode (1:ℂ)).part s
    simp only [Poly.part_smul,Poly.part_send]
    split <;> simp
  rw [Spill.Foundry.uncut,all.tsum_eq]
  simp [Poly.part_send]

end YM.Integration.WilsonCapturedPrimaryPointIncome
