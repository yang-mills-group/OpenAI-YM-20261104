import YM.Integration.WilsonGraphFiniteOrdinaryWordMass
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeBook

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Integration.GradedFar.AppointedOrdinaryWordMass

open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets
open FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine FVA2.GradedFar.Cart Window Batch
open YM.Integration.WilsonGraphUniformMixedShapeMass
open scoped Topology BigOperators ContDiff Classical

variable (g : YangMills.GaugeGroup) {C : Family g.core} {f : Extraction.Order}
variable {S : Table C.book} (F : Final C f S) (J P : ℝ → tower S)
variable (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z : WilsonPrescription g.core)
variable (M : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
variable {hG : g.core.Simple} {σ : MS.Land.Prescription (Press.portDeck g.core)}
variable (H : Main.Match Z hG M σ true) (ν : ℝ) {t : ℝ → ℝ}
variable (ht : Coupling g.core t) (Hp : Prepared F J P Z t)
variable {n h hin : ℕ} {e : Fin n → ℕ} (he : AppointedH140Through hin e)
variable (Hn : ∀ k, Window.Regained F P R (Scale.Measure.outlook Z.scheme Z.criterion) t n k h)
variable (α : ∀ k, Future g.core k) (hα : ∀ k, PaidFuture F P (α k) t)
variable {K : Set (Points n)} (hK : IsCompact K) (hx : K ⊆ conf n)

include H ht Hp Hn hα he hK hx

/-- The native #140 signed word, on the original physical packet and MS vector,
with one price before all centers, all input labels and all contractive output duals. -/
theorem onReader (word : TraceOrder n) (q : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points n), x ∈ K →
      ∀ (v : AppointedH140Inputs g.core e) (out : Sec g.core h →ₗ[ℂ] ℂ),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ‖δ word (fun y => out (packet F P R h o r y v)) x -
        δ word (fun y => out (msVector Z M ν v y q h (t r))) x‖ ≤
        A * inputMass g (d := e) v * |t r|^(q+1) := by
  let E (r : ℝ) (j : E4 × K) (v : AppointedH140Inputs g.core e) (l : Toon g.core h) :=
    δ word (fun y => messenger F P R j.1 r l y v) j.2.val -
      appointedH140Crop q (t r) (liability Z l v j.2.val word)
  have expand : ∀ᶠ r in trail, ∀ (j : E4 × K) (v : AppointedH140Inputs g.core e) (l : Toon g.core h),
      E r j v l = ∑ b : Picks g.core e, multipliers v b * E r j (basisWord b) l := by
    filter_upwards [near_collar F R n h hK hx] with r eligible j v l
    dsimp only [E]
    rw [Batch.messenger_levy F P R l word v j.1 r (eligible _ j.2.property j.1),
      AppointedDerivativeBook.levy F J P R Z M H ht Hp l Hn α hα he word v (hx j.2.property),
      map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← PowerSeries.smul_eq_C_mul, map_smul, smul_eq_mul, mul_sub]
  have basis (l : Toon g.core h) (b : Picks g.core e) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in trail, ∀ j : E4 × K,
        ‖E r j (basisWord b) l‖ ≤ C * |t r|^(q+1) := by
    obtain ⟨C, hC, paid⟩ :=
      ((Window.mixedCosts F P R Z M H l ht Hn Hp.connects α hα hK hx he (basisWord b) word).good q).cost
    refine ⟨C, hC, ?_⟩
    filter_upwards [paid] with r current j
    simpa only [E, alarm] using current j
  obtain ⟨A, hA, common⟩ := finitePrice g e h q trail t E expand basis
  refine ⟨A, hA, ?_⟩
  filter_upwards [common, near_collar F R n h hK hx] with r price eligible o x present v out contract
  have physical (l : Toon g.core h) : ContDiffOn ℝ ∞
      (fun y => coord l (packet F P R h o r y v)) {y | arena F R h o r y} :=
    fun y hy => by simpa only [alarm] using (breeze F P R o r l y hy v).contDiffWithinAt (s := {y | arena F R h o r y})
  have formal (l : Toon g.core h) : ContDiffOn ℝ ∞
      (fun y => coord l (msVector Z M ν v y q h (t r))) (conf n) := by
    simp_rw [bookVector Z M H ν, cargo_crop, crop_eq]
    exact ContDiffOn.sum (fun k _ => contDiffOn_const.mul
      (AppointedDerivativeBook.lit F J P R Z M H ht Hp l Hn α hα he v k))
  rw [dualWord g _ out word (season_open F R h o r n) physical (eligible x present o),
    dualWord g _ out word (conf_open n) formal (hx present), ← Finset.sum_sub_distrib]
  simp_rw [AppointedDerivativeBook.creed F J P R Z M H ν ht Hp _ Hn α hα he v word q (t r) (hx present),
    ← mul_sub]
  simpa only [E, alarm] using price (o, ⟨x, present⟩) v out contract

end YM.Integration.GradedFar.AppointedOrdinaryWordMass
