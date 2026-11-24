import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedUnselectedRiverFiling
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCenteredSourceOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace YM.FVA2.GradedFar.Physical.AppointedTwoRoundedRows
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O.Score O.Enh
open Continuation Continuation.Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : Register.WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J : FramesH P) (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (t : ℝ → ℝ)

variable {U J Q N M t} {K : Set (Points n)} {S : Set (Points m)}
variable (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
    (old : OldCost U J Q) (frame : Scaled N M J t)
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
include H ht hK hx

include old frame

theorem measuredAtPositiveCrops (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ)
    (numerator : ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
      RoundedAt N (Y0 U J d (fun _ : Fin 1 => h)) (upper G 1 B) K {RootG} t p)
    (centered : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      RoundedAt N (Y0 U J (fun _ : Fin 1 => h) (fun _ : Fin 1 => h))
        (upper G 1 B) {(0 : Points 1)} {RootG} t p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View U, ∀ x∈K, ∀ u : Inputs G d, Within L u →
      Ball (D*t r^(q+1)) (packet U J Q d h r i x u - Wave.cropped N M x u h q (t r)) := by
  let S : Set (Points 1):={RootG}; let e:Fin 1→ℕ := fun _ => h
  have hy : S ⊆ O.Enh.Outside 1 := singleton_subset_iff.mpr ok_wall
  obtain ⟨L',hl,hw⟩ := Continuation.Margin.probes_fit G h
  obtain ⟨D,hD,hc⟩ := old _ _ hn d e h K S hK hx isCompact_singleton hy L L' 1 one_pos
  let η:ℝ := 1/2
  obtain ⟨B,hB,hb⟩ := (Continuation.Stretch.can_stiffen (q+1) (show η<1 by norm_num [η]) D).exists
  obtain ⟨p,hp,hq⟩ := ((Continuation.Stretch.can_deepen (q+1) B h h η).and (eventually_ge_atTop (max 1 q))).exists
  have hv := frame h p B 1 hb one_pos
  have hf := numerator p ((le_max_left 1 q).trans hq) B hb
  have hi := centered p B hb
  exact Wave.coefficient H t ht hK hx zero_lt_one le_rfl hb hp (show 0<η by norm_num[η]) le_rfl ((le_max_right 1 q).trans hq)
    (Eventually.of_forall fun w i b => ⟨receive U J w i _ _ h,funext fun a => ((receive_leg U J ..).trans (center_same U J ..)).symm⟩)
    hv hf hi (hc B hb) hw hD hB
end
end YM.FVA2.GradedFar.Physical.AppointedTwoRoundedRows


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

section Paper
universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)

theorem onPositiveNumerator {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (numerator : ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
      Filing (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) d (fun _ : Fin 1 => h) K {RootG} (upper g.core 1 B) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) (Physical.packet (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P d h r i x u -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨frame,history⟩ := electedCosts.{u} g hg dates strictDates
  exact Physical.AppointedTwoRoundedRows.measuredAtPositiveCrops (WilsonGraphPaperPublication.perspective.{u} g hg).matching
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg dates strictDates) history frame hK hx L hn d h q
    (fun p hp B hB => rounded (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J) _ _ _ _ _ (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) p (numerator p hp B hB))
    (fun p B hB => AppointedCenteredRounded.roundedAt.{u} g hg dates strictDates h p {RootG}
      isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB)

end Paper
end
end YM.FVA2.GradedFar.AppointedTwoFiledPayments


namespace YM.FVA2.GradedFar.AppointedTwoFiledPublicRows
noncomputable section
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YangMills YM.Answer.ContinuumLimit YM.Integration Asymptotics
open scoped Topology BigOperators Classical ContDiff

universe u v
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev U := (V.{u} g hg periods strict).pupil.last
private abbrev frame := Elected.Hframe (N g hg) (U.{u} g hg periods strict) (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

/-- The finite fiscal roster is registered at the original unselected viewer and origin. -/
structure UnselectedIncome {n : ℕ} (d : Fin n → ℕ) (h p : ℕ) (X : Set (YM.Points n)) (B : ℝ) where
  coupons : Type v
  finite : Fintype coupons
  events : Type v
  river : Filter events
  radius : events → ℝ
  rowValue : coupons → events → ℂ
  reportedCrop : coupons → events → ℂ
  fileHeat : coupons → events → ℝ
  title : coupons → events → PowerSeries ℂ
  cap : ℕ
  nearCap : ∀ i, d i ≤ cap
  farCap : ∀ _ : Fin 1, h ≤ cap
  price : ∀ s, (fun i => rowValue s i - reportedCrop s i) =O[river]
    (fun i => (meter g.core (radius i))^(p+1))
  onLayout : ∀ L R : ℝ, ∃ select : AppointedFiledMeter.Layout g.core d (fun _ : Fin 1 => h)
        (View (U.{u} g hg periods strict)) X {RootG} L R → coupons,
    ∃ arrive : AppointedFiledMeter.Layout g.core d (fun _ : Fin 1 => h)
        (View (U.{u} g hg periods strict)) X {RootG} L R → events,
      Tendsto arrive (Filter.comap AppointedFiledMeter.Layout.w (windows (upper g.core 1 B))) river ∧
      ∀ᶠ l in Filter.comap AppointedFiledMeter.Layout.w (windows (upper g.core 1 B)),
        radius (arrive l) = l.w.len ∧
        rowValue (select l) (arrive l) = Physical.Y0 (U.{u} g hg periods strict)
          (frame.{u} g hg periods strict) d (fun _ : Fin 1 => h) l.w (none,0) l.x l.y l.u l.v ∧
        fileHeat (select l) (arrive l) = heat.{u} g hg periods strict l.w.len ∧
        reportedCrop (select l) (arrive l) =
          crop p (fileHeat (select l) (arrive l)) (title (select l) (arrive l)) ∧
        ∃ safe : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+1),
          ∀ j ≤ p, coeff j (title (select l) (arrive l)) =
            Measure.outlook (N g hg).scheme (N g hg).criterion cap _
              ⟨forest l.x (squeeze (-l.w.sep) l.y),safe⟩ j
              (Fin.append (installedInputs nearCap l.u) (installedInputs farCap l.v))

theorem filing {n : ℕ} (d : Fin n → ℕ) (h p : ℕ) {X : Set (YM.Points n)}
    (hX : IsCompact X) (hx : X ⊆ conf n) {B : ℝ} (hB : 0<B)
    (income : UnselectedIncome.{u,v} g hg periods strict d h p X B) :
    AppointedTwoFiledPayments.Filing (N g hg) (U.{u} g hg periods strict) (frame.{u} g hg periods strict)
      d (fun _ : Fin 1 => h) X {RootG} (upper g.core 1 B) (heat.{u} g hg periods strict) p := by
  letI := income.finite
  exact AppointedTwoFiledPayments.filingAtZero.{u} g hg periods strict d h p income.cap
    hX hx isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB income.nearCap income.farCap
    income.river income.radius income.rowValue income.reportedCrop income.fileHeat income.title
    income.price income.onLayout

theorem onUnselectedIncomes {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
    (incomes : ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
      UnselectedIncome.{u,v} g hg periods strict d h p K B)
    :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ o : E4, ∀ x∈K, ∀ u : Inputs g.core d, Within L u →
      Ball (D*((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)^(q+1)) ((show Sec g.core h from (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun j => ⟨d j, u j⟩) o x) -
        Wave.cropped (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x u h q ((WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r)) := by
  obtain ⟨D,hD,paid⟩ := AppointedTwoFiledPayments.onPositiveNumerator.{u} g hg periods strict hn d h q hK hx L
    (fun p hp B hB => filing.{u,v} g hg periods strict d h p hK hx hB (incomes p hp B hB))
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx₀ u hu
  rw [readerValue.{u} g hg periods strict d u h r (none,o) x]
  exact hr (none, o) x hx₀ u hu


end
end YM.FVA2.GradedFar.AppointedTwoFiledPublicRows

