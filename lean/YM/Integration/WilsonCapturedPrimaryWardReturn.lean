import YM.Integration.WilsonCapturedPrimaryWardFaces
import YM.Integration.WilsonCapturedPrimaryActiveArms

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardReturn
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open Bandage Stock RG16.Literal RG05Readout Native Address Many Records Harvest Copper
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Accent Motion
open Trace.Physical.GermGraph GridApprox Next.Rank Ribbon Trace.Physical
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Cards OPE.Orbits Spec
open WilsonPositionThermometerCapStation WilsonOffsetReportingProducts WilsonOffsetEquationLaw
open WilsonAddressedEquationShelf WilsonCapturedPrimaryPhysicalArray WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryFaceWallet WilsonThermometerOwnOffsetField WilsonReflectedPhysicalRate
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n N p k u h : ℕ}
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

/-- The earlier filed field is that of the complete projected physical face. -/
def Restored (d : Fin n → ℕ) (o : Fin n → Site (R.family.side N p))
    (S : Shelf (N:=N) (p:=p) R k d o) (kn : k ≤ N) (un : u ≤ N) (J : ℕ)
    (door : Opened R.family h u p) (fee : ℝ) : Prop :=
  ∀ (s : Finset (Fin n)) (x : (i : Fin n) → R.family.label (d i))
    (y : (i : Fin n) → Palette R.family (level d s i)),
    WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level d s) (S.paths s) kn
      (label R s (fun i=> b.step (d i) (N,p) (x i))) y →
    let H := WilsonCapturedPrimaryWardFaces.projected R b d x s o
    let A := WilsonCapturedPrimaryWardFaces.adjusted R V P b d x s o
    let c := WilsonMacroscopicRichChildRegistration.returned R.family R.makes door un H
    let price := (((∏ i ∈ s, (1+size (y i)))*2^(n-s.card))*fee)
    Booked R.family N p h H u un ∧
    PaidAt R.family.S N p J (R.family.beta N p) price
      (WilsonCapturedPrimaryScaledCounter.difference R door un H) ∧
    PaidAt R.family.S N p J (R.family.beta N p) price (A-R.family.O N p c 0)

variable [NeZero n]
theorem original (simple : G.Simple) (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (slow : WilsonWindowReportingPace.Slow R.kit)
    (D v h J u : ℕ) (wide : 4 < v) (enlarged : R.family.ref h ≤ J)
    (station : ∀p, Opened R.family h u p) (tiling : Stock.Tabs.opens R.family.path.levels 1 J u)
    (φ : Test n) (d : Fin n → ℕ) (cap : ∀i,d i ≤ D)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, let m := capture R r
    let k := launch R simple v r
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (z : Fin n → Site (R.family.side N p)),
      WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 → ∀ ax : Fin n,
      ∃ S : Shelf (N:=N) (p:=p) R k d (registered z (some ax)),
        S.serves kn.le (um.trans (m.le_succ.trans (mk.le.trans kn.le))) J (station p) (K*r^((h:ℝ)+1/32)) ∧
        Restored R V P b d (registered z (some ax)) S kn.le
          (um.trans (m.le_succ.trans (mk.le.trans kn.le))) J (station p) (K*r^((h:ℝ)+1/32)) := by
  obtain ⟨K,one,sale⟩ := WilsonCapturedPrimaryActiveArms.original R simple book shop slow D v h J u
    wide enlarged station tiling φ d cap
  have matched := WilsonCapturedPrimaryWardFaces.original R V W P b portfolio issued simple slow v J h wide d φ
  refine ⟨K,one,?_⟩
  filter_upwards [sale,matched] with r bought compare
  obtain ⟨um,mk,all⟩ := bought
  refine ⟨um,mk,?_⟩
  intro N p kn z nz ax
  obtain ⟨S,ready⟩ := all N p kn z nz ax
  refine ⟨S,ready,?_⟩
  intro s x y hit
  obtain ⟨booked,paid⟩ := ready s (fun i=>b.step (d i) (N,p) (x i)) y hit
  refine ⟨booked,paid,?_⟩
  let H := WilsonCapturedPrimaryWardFaces.projected R b d x s (registered z (some ax))
  let un := um.trans ((capture R r).le_succ.trans (mk.le.trans kn.le))
  let c := WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) un H
  have exactTest := compare N p kn.le paid.live z nz (some ax) s x c
  exact ⟨paid.live,exactTest.1,exactTest.2.le.trans paid.mark⟩

end YM.Integration.WilsonCapturedPrimaryWardReturn
