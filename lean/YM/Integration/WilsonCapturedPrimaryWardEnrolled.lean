import YM.Integration.WilsonCapturedPrimaryWardSeats

/-! On the common reflected shelf, the pupil takes all projected slots together.
The signed Wilson measurement uses the counterterm filed on that very product. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardEnrolled
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open Bandage Stock RG16.Literal RG05Readout Native Address Many Records Harvest Copper
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Accent Motion
open Trace.Physical.GermGraph GridApprox Next.Rank Ribbon Trace.Physical
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Cards OPE.Orbits Spec
open WilsonCapturedPrimaryPhysicalArray WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryFaceWallet WilsonThermometerOwnOffsetField WilsonReflectedPhysicalRate
open WilsonCapturedPrimaryWardRestoration
open scoped Classical Topology BigOperators
open Table Spec Trace RG17 PhysMS PhysMS.Frame Maxwell XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {T : Table R.family.book}
    {l : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
variable (F : Final R.family f T) (J : ℝ → PhysMS.tower T) (O : Store G) (A : ℝ → Group R.family 6)
variable (V : ∀d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

open WilsonCapturedPrimaryWardAppointment (share trimmed)
open WilsonCapturedPrimaryWardThermometer (input)
open WilsonThermometerIntrinsicRoster
open Marker Extra.Multi

variable {R} {N p k n : ℕ} {d : Fin n→ℕ} {o : Fin n→Site (R.family.side N p)}

def Fine (t : ℕ) (S : Shelf (N:=N) (p:=p) R k d o) (live:k≤N)
    (v:(i:Fin n)→R.family.label (d i)) (y:(i:Fin n)→Palette R.family (d i)) : Prop :=
  let names:=Stock.census (Fin n)
  WilsonThermometerIntrinsicRoster.filed R d o (trimmed R d y) S.viewer S.route names live t ∧
    ∀ i (under:i≤N) (s:names.Mode),
      (fun U=>(WilsonThermometerIntrinsicRoster.density R d o (trimmed R d y) S.route names live under U).part s) =
      (∏ j∈s.val,share R d y j) • (fun U=>(gust R.family.path N p N
        (WilsonCapturedPrimaryWardAppointment.input R d o v names) i under U).part s)

variable (R)

theorem original (room : CellHyp R.family f) (simple : G.Simple)
    (physical : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v h j u : ℕ) (wide : 4 < v) (enlarged : R.family.ref h ≤ j)
    (station : ∀p, Opened R.family h u p) (tiling : Stock.Tabs.opens R.family.path.levels 1 j u)
    (φ : Test 3) (portfolio : ∀d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ t : ℕ, 9≤t ∧ ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, let m := capture R r
    let k := launch R simple v r
    let Z := adjusted F J O A r
    let d := fun i : Fin 3=>(grade i).val
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ᶠ z : ℕ × ℕ in f.fuse,
    ∃ kn : k < z.1, ∀ o : Fin 3 → Site (R.family.side z.1 z.2),
      WilsonCenteredCompactBooking.mass R φ r z o ≠ 0 → ∀ ax : Fin 3,
      ∃ S : Shelf (N:=z.1) (p:=z.2) R k d (registered o (some ax)),
      let un := um.trans (m.le_succ.trans (mk.le.trans kn.le))
      let w := K*r^((h:ℝ)+1/32)
      S.serves kn.le un j (station z.2) w ∧
      ∀ (τ : Badge) (y : (i:Fin 3) → Palette R.family (d i)), let x:=input R Z z τ
        let v := fun i=>b.step (d i) z (x i)
        WilsonCapturedPrimaryNamedReturn.primary R (p:=z.2) d S.route kn.le v y →
        Fine t S kn.le v y ∧ ∀ s:Finset (Fin 3),
          let Y := WilsonCapturedPrimaryWardFaces.projected R b d x s (registered o (some ax))
          let c := WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station z.2) un Y
          Booked R.family z.1 z.2 h Y u un ∧ PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2)
            ((((∏ i∈s,(1+size (y i)))*2^(3-s.card))+1)*w)
            (WilsonCapturedPrimaryWardRestoration.filed R d x s (registered o (some ax))-R.family.O z.1 z.2 c 0) := by
  let d:=fun i:Fin 3=>(grade i).val
  have cap (i:Fin 3):d i≤6 := Nat.le_of_lt_succ (grade i).isLt
  obtain ⟨t,tt,date⟩ := WilsonCapturedPrimaryWardAppointment.original R simple shop 6
  obtain ⟨K,one,paid⟩ := WilsonCapturedPrimaryWardThermometer.original R F J O A V W P b room simple physical
    lead book shop slow v h j u wide enlarged station tiling φ portfolio issued
  refine ⟨t,tt,K,one,?_⟩
  have go := WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple v (by omega)
  have rooms := WilsonCapturedPrimaryWardSeats.separation R simple slow v wide φ
  filter_upwards [paid,go.eventually date,rooms] with r current fund apart
  obtain ⟨um,mk,represented⟩ := current
  refine ⟨um,mk,?_⟩
  filter_upwards [represented] with z found
  obtain ⟨kn,fields⟩ := found
  refine ⟨kn,?_⟩
  intro o live ax
  obtain ⟨S,serve,probes⟩ := fields o live ax
  refine ⟨S,serve,?_⟩
  intro τ y
  dsimp only
  intro paidLift
  let x:=input R (adjusted F J O A r) z τ
  let v₀:=fun i=>b.step (d i) z (x i)
  have fine := fund z.1 z.2 kn.le 3 d cap (registered o (some ax)) (apart z.1 z.2 kn.le o live ax)
    S (Stock.census (Fin 3)) v₀ y paidLift
  refine ⟨fine,?_⟩
  intro s
  obtain ⟨booked,paid⟩ := probes τ s (WilsonCapturedPrimaryWardSeats.filled S kn.le y s)
    (WilsonCapturedPrimaryWardSeats.legal S kn.le v₀ y paidLift s)
  rw [WilsonCapturedPrimaryWardSeats.occupied_size] at paid
  exact ⟨booked,paid⟩

end YM.Integration.WilsonCapturedPrimaryWardEnrolled
