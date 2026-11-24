import YM.Integration.WilsonCapturedPrimaryWardActualFiling
import YM.Integration.WilsonThermometerMarchReference

/-! At the oriented physical station, the finite coordinates of all three thermometer
fields have a common bound before either regulator. Restore the original Wilson
fields against the genuine earlier report of the projected face on the same tiling. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardThermometer
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

/-- The three literal cutoff fields on the one corrected physical station. -/
abbrev input (Z : Group R.family 6) (z : ℕ×ℕ) (s : Badge) (i : Fin 3) :
    R.family.label (grade i).val := Z.station.wheel.atCut z (index Z (grade i)) (vector Z s i)

private def bill (r : ℝ) (t : Badge×Fin 3) : ℝ :=
  |Real.exp (1*(-Real.log r))*WilsonThermometerMarchReference.fee R.family t.1 t.2|

private theorem capBill (r : ℝ) (τ : Badge) (i : Fin 3) :
    Real.exp (1*(-Real.log r))*WilsonThermometerMarchReference.fee R.family τ i ≤
      ∑ t : Badge×Fin 3, bill R r t := by
  refine (le_abs_self _).trans ?_
  change bill R r (τ,i) ≤ _
  exact Finset.single_le_sum (f:=bill R r) (fun t _=>show 0≤bill R r t from abs_nonneg _) (Finset.mem_univ (τ,i))

theorem wallet (simple : G.Simple) (paid : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J)
    (lead : Leading F J) :
    ∀ᶠ r in trail, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z : ℕ×ℕ in f.fuse,
      ∀ (τ : Badge) (i : Fin 3), ‖input R (adjusted F J O A r) z τ i‖ ≤ M := by
  have refs := WilsonThermometerMarchReference.original F J O A simple paid lead 1 zero_lt_one
  have top : Tendsto Prod.fst f.fuse atTop :=
    tendsto_atTop.mpr fun n=>(f.fused _).2 (Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop n)
  filter_upwards [refs] with r reference
  let Z:=adjusted F J O A r
  refine ⟨∑ t : Badge×Fin 3,bill R r t,Finset.sum_nonneg (fun t _=>show 0≤bill R r t from abs_nonneg _),?_⟩
  filter_upwards [top.eventually (eventually_gt_atTop Z.station.k)] with z later
  intro τ i
  have sized : ‖input R Z z τ i‖ ≤ (R.family.labels.level (grade i)).coeffSize (input R Z z τ i) :=
    (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg _ _)).mpr fun j=>
      Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
  exact sized.trans ((reference z.1 z.2 later τ i).trans (capBill R r τ i))

theorem original (room : CellHyp R.family f) (simple : G.Simple)
    (physical : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v h j u : ℕ) (wide : 4 < v) (enlarged : R.family.ref h ≤ j)
    (station : ∀p, Opened R.family h u p) (tiling : Stock.Tabs.opens R.family.path.levels 1 j u)
    (φ : Test 3) (portfolio : ∀d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, let m := capture R r
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
      ∀ (τ : Badge) (s : Finset (Fin 3)) (y : (i:Fin 3) → Palette R.family (level d s i)),
        let x := input R Z z τ
        WilsonCapturedPrimaryNamedReturn.primary R (p:=z.2) (level d s) (S.paths s) kn.le
          (label R s (fun i=>b.step (d i) z (x i))) y →
        let Y := WilsonCapturedPrimaryWardFaces.projected R b d x s (registered o (some ax))
        let c := WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station z.2) un Y
        Booked R.family z.1 z.2 h Y u un ∧ PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2)
          ((((∏ i∈s,(1+size (y i)))*2^(3-s.card))+1)*w)
          (filed R d x s (registered o (some ax))-R.family.O z.1 z.2 c 0) := by
  let d := fun i : Fin 3=>(grade i).val
  have cap (i:Fin 3) : d i ≤ 6 := Nat.le_of_lt_succ (grade i).isLt
  obtain ⟨K,one,paid⟩ := WilsonCapturedPrimaryWardActualFiling.original R V W P b room simple book shop slow
    6 v h j u wide enlarged station tiling φ d cap portfolio issued
  refine ⟨K,one,?_⟩
  have available := wallet R F J O A simple physical lead
  filter_upwards [paid,available,show ∀ᶠ r : ℝ in trail, 0<r from self_mem_nhdsWithin] with r incoming priced hr
  let Z := adjusted F J O A r
  obtain ⟨M,nonnegative,funded⟩ := priced
  let w := K*r^((h:ℝ)+1/32)
  have wpos : 0<w := mul_pos (zero_lt_one.trans_le one) (Real.rpow_pos_of_pos hr _)
  obtain ⟨um,mk,seen⟩ := incoming
  refine ⟨um,mk,?_⟩
  filter_upwards [seen M nonnegative w wpos,funded] with z tested price
  obtain ⟨kn,fields⟩ := tested
  refine ⟨kn,?_⟩
  intro o live ax
  obtain ⟨S,serve,read⟩ := fields o live ax
  refine ⟨S,serve,?_⟩
  intro τ s y
  dsimp only
  intro hit
  obtain ⟨booked,charged⟩ := read s (input R Z z τ) y (fun i _=>price τ i) hit
  exact ⟨booked,by simpa only [add_mul,one_mul] using charged⟩

end YM.Integration.WilsonCapturedPrimaryWardThermometer
