import YM.Integration.WilsonCapturedPrimaryFiledArms
import YM.Integration.WilsonCapturedPrimaryScaledCounter
import YM.Integration.WilsonCapturedPrimarySpatialFunds

/-! A literal registered cutoff product and its own earlier field. The
filing keeps the price of each actual calibrated input coordinate. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryNamedReturn
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonReflectedPhysicalFiling (Arms reading)
open WilsonThermometerOwnOffsetField OPE.Cards
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
variable (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {n : ℕ} [NeZero n]
local notation "C" => R.family
local notation "origin" z:max ax:max => WilsonCapturedPrimaryPhysicalArray.registered z (some ax)

def field {N p : ℕ} (d : Fin n → ℕ) (x : (i : Fin n) → (C).label (d i))
    (sites : Fin n → Site ((C).side N p)) : Cut C N p := fun U => ∏ i, (C).O N p (x i) (sites i) U

def primary {N p k : ℕ} (d : Fin n → ℕ) (r : (i : Fin n) → Emblems C (d i)) (live : k ≤ N)
    (x : (i : Fin n) → (C).label (d i)) (y : (i : Fin n) → Palette C (d i)) : Prop :=
  ∀ i, ((C).factory (d i) N p).terminal (finer (r i) live (y i) (primaryLetter (d i))) =
       (((C).S.a k : ℂ)^(d i))⁻¹ • x i

omit [NeZero n] in
theorem sparse {N p k : ℕ} (d : Fin n → ℕ) (r : (i : Fin n) → Emblems C (d i)) (live : k ≤ N)
    (x : (i : Fin n) → (C).label (d i)) :
    primary R (p:=p) d r live x (fun i => WilsonNeutralOffsetCutoff.input R (p:=p) (r i) live (x i)) :=
  fun i => WilsonNeutralOffsetCutoff.launched R (r i) live (x i)

omit [NeZero n] in
theorem sale {N p k u J h D : ℕ} (d : Fin n → ℕ) (cap : ∀ i, d i ≤ D)
    (sites : Fin n → Site ((C).side N p)) (V : (i : Fin n) → Sight C (d i) p)
    (r : (i : Fin n) → Emblems C (d i)) (entry : WilsonCapturedPrimaryFiledArms.entered R d sites (k:=k) V r)
    (kn : k ≤ N) (un : u ≤ N) (door : Opened C h u p) (x : (i : Fin n) → (C).label (d i))
    (y : (i : Fin n) → Palette C (d i)) (hit : primary R (p:=p) d r kn x y) (fee : ℝ)
    (budget : let f := reading R (WilsonCapturedPrimaryFiledArms.arm R d sites cap V r entry y) kn
      Booked C N p h f u un ∧ PaidAt (C).S N p J ((C).beta N p) fee
        (WilsonCapturedPrimaryScaledCounter.difference R door un f)) :
    let Y := field R d x sites
    Booked C N p h Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
      (WilsonCapturedPrimaryFiledArms.rent R d y * fee) (WilsonCapturedPrimaryScaledCounter.difference R door un Y) := by
  let F := reading R (WilsonCapturedPrimaryFiledArms.arm R d sites cap V r entry y) kn
  let W := WilsonCapturedPrimaryFiledArms.rent R d y
  have wpos : 0 < W := WilsonCapturedPrimaryFiledArms.positive R d y
  have eq : F = ((W:ℂ)⁻¹) • field R d x sites :=
    WilsonCapturedPrimaryFiledArms.read R d sites cap V r entry kn x y hit
  have restored : (W:ℂ) • F = field R d x sites := by
    rw [eq, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr wpos.ne'), one_smul]
  have continuousF : Continuous F := by
    rw [eq]
    exact (continuous_finsetProd _ (fun i _ => (C).continuousO N p _ (x i) (sites i))).const_smul _
  have res := WilsonCapturedPrimaryScaledCounter.original R door un F continuousF budget.1
    (W:ℂ) budget.2
  rw [restored] at res
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos wpos] using res

include simple book in
theorem original (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (slow : WilsonWindowReportingPace.Slow R.kit) (D v h J u : ℕ) (wide : 4 < v)
    (enlarged : (C).ref h ≤ J) (station : ∀p, Opened C h u p)
    (tiling : Stock.Tabs.opens (C).path.levels 1 J u) (φ : Test n)
    (d : Fin n → ℕ) (cap : ∀i,d i ≤ D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ radius in trail,
    let m := capture R radius
    let k := launch R simple v radius
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (z : Fin n → Site ((C).side N p)),
      WilsonCenteredCompactBooking.mass R φ radius (N,p) z ≠ 0 → ∀ ax : Fin n,
      ∃ (V : (i : Fin n) → Sight C (d i) p) (r : (i : Fin n) → Emblems C (d i)),
        WilsonCapturedPrimaryFiledArms.entered R d (origin z ax) (k:=k) V r ∧
        ∀ (x : (i : Fin n) → (C).label (d i)) (y : (i : Fin n) → Palette C (d i)),
        primary R (p:=p) d r kn.le x y →
        let un := um.trans (m.le_succ.trans (mk.le.trans kn.le))
        let Y := field R d x (origin z ax)
        Booked C N p h Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
         (WilsonCapturedPrimaryFiledArms.rent R d y * (K * radius^((h:ℝ)+1/32)))
         (WilsonCapturedPrimaryScaledCounter.difference R (station p) un Y) := by
  obtain ⟨Z,K,one,_,_,sold⟩ := WilsonCapturedPrimarySpatialFunds.original R simple book shop slow
    D v h J u wide enlarged station tiling φ
  have launches := (WilsonReflectedPhysicalRate.dates R simple slow v (by omega)).2.grows
  refine ⟨K,one,?_⟩
  filter_upwards [sold, launches.eventually (WilsonCapturedPrimaryFiledArms.election R d simple shop)]
    with radius readingAt seat
  obtain ⟨um,mk,gate⟩ := readingAt
  refine ⟨um,mk,?_⟩
  intro N p kn z active ax
  obtain ⟨V,r,entry⟩ := seat N p kn.le (origin z ax)
  refine ⟨V,r,entry,?_⟩
  intro x y hit
  let a := WilsonCapturedPrimaryFiledArms.arm R d (origin z ax) cap V r entry y
  obtain ⟨q,t,terms,interior,price⟩ := gate N p kn z active ax a rfl
  apply sale R d cap (origin z ax) V r entry kn.le _ (station p) x y hit _
  exact ⟨terms.works u le_rfl um, tiling.1.trans (um.trans (Nat.le_succ _ |>.trans (mk.le.trans kn.le))), interior, price⟩

end YM.Integration.WilsonCapturedPrimaryNamedReturn
