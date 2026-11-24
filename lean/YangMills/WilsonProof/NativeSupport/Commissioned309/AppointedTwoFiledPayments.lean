import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedFiledMeterRows
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedRadialCurrency
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedTwoRoundedRows
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPhysicalWindowAndPhase

namespace YM.FVA2.GradedFar.AppointedTwoFiledPayments
noncomputable section
set_option maxHeartbeats 4000000
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n m : ℕ} {A : Family G} {o : Extraction.Order} {P : Table A.book}

def Filing (N : Register.WilsonPrescription G) (U : Spec.Final A o P) (H : FramesH P)
    (d : Fin n → ℕ) (e : Fin m → ℕ) (K : Set (Points n)) (S : Set (Points m))
    (windowsPaid : Set Window) (t : ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ cap : ℕ, ∃ hd : ∀ i, d i ≤ cap, ∃ he : ∀ i, e i ≤ cap,
    ∀ L R : ℝ, ∃ rowRead : AppointedFiledMeter.Layout G d e (View U) K S L R → ℂ,
      ∃ stamps : AppointedFiledMeter.Layout G d e (View U) K S L R → PowerSeries ℂ,
      ∃ fileClock : AppointedFiledMeter.Layout G d e (View U) K S L R → ℝ,
      ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ l in Filter.comap AppointedFiledMeter.Layout.w (windows windowsPaid),
        rowRead l = Physical.Y0 U H d e l.w l.viewer l.x l.y l.u l.v ∧
        fileClock l = t l.w.len ∧
        (∃ hc : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+m),
          ∀ j ≤ p, coeff j (stamps l) =
            Measure.outlook N.scheme N.criterion cap _ ⟨forest l.x (squeeze (-l.w.sep) l.y),hc⟩ j
              (Fin.append (installedInputs hd l.u) (installedInputs he l.v))) ∧
        ‖rowRead l-crop p (fileClock l) (stamps l)‖ ≤ C*(meter G) l.w.len^(p+1)*(1+l.w.sep)^a

theorem radialTransfer (G : Gauge) (W : Set Window) (p : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ w in windows W, 0 ≤ 1+Window.sep w ∧
      (meter G (Window.len w))^(p+1) ≤ M*(gYM G (Window.len w))^(p+1) := by
  refine ⟨1,zero_lt_one,?_⟩
  filter_upwards [(windows_separation W).eventually_ge_atTop (0:ℝ)] with w hw
  exact ⟨add_nonneg zero_le_one hw, by rw [AppointedRadialCurrency.price,one_mul]⟩

theorem rounded (N : Register.WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {simple : G.Simple} {prescription : MS.Land.Prescription (Press.portDeck G)}
    (agreement : Main.Match N simple M prescription true) (U : Spec.Final A o P) (H : FramesH P)
    (d : Fin n → ℕ) (e : Fin m → ℕ) (K : Set (Points n)) (S : Set (Points m))
    (W : Set Window) (t : ℝ → ℝ) (p : ℕ) (filed : Filing N U H d e K S W t p) :
    RoundedAt N (Physical.Y0 U H d e) W K S t p := by
  obtain ⟨cap,hd,he,price⟩ := filed
  exact AppointedFiledMeter.roundedOnFiled N agreement U H K S W p cap hd he t (meter G)
    (radialTransfer G W p) price

section Paper
universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)

theorem electedCosts :
    Scaled (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) ∧ OldCost (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P :=
  ⟨Physical.learned (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg))
      (AppointedPhysicalWindowAndPhase.earned.{u} g hg dates strictDates),
   Physical.paid_history (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg))
      (AppointedPhysicalWindowAndPhase.earned.{u} g hg dates strictDates)
      (Elected.stocked (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.VFrame.2
        (Appointed1859PreAmple.ample (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg))).2
      (Appointed1860G6.retained.{u} g hg dates strictDates).2.2.2.2.1⟩

theorem ordinary {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (numerator : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 1 => h) K {RootG} (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p)
    (centered : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (fun _ : Fin 1 => h) (fun _ : Fin 1 => h) {(0 : Points 1)} {RootG}
        (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) (Physical.packet (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P d h r i x u -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨frame,history⟩ := electedCosts.{u} g hg dates strictDates
  exact Physical.AppointedTwoRoundedRows.measuredFromTwoRows (WilsonGraphPaperPublication.perspective.{u} g hg).matching
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg dates strictDates) history frame hK hx L hn d h q
    (fun p B hB => rounded (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) _ _ _ _ _ (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p (numerator p B hB))
    (fun p B hB => rounded (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) _ _ _ _ _ (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p (centered p B hB))

theorem emptyExterior {n : ℕ} (d : Fin n → ℕ) (p : ℕ) {K : Set (Points n)} (L : ℝ)
    (filed : Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 0 => 0) K {0} (upper g.core 1 1) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      ‖Physical.alone (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) i r x u - crop p ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r) (Wave.value (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u)‖ ≤ D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(p+1) :=
  Physical.AppointedTwoRoundedRows.kernelFromEmptyExterior (WilsonGraphPaperPublication.perspective.{u} g hg).matching
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg dates strictDates) L d p
    (rounded (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) _ _ _ _ _ (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p filed)

end Paper
end
end YM.FVA2.GradedFar.AppointedTwoFiledPayments

