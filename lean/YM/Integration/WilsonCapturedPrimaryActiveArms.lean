import YM.Integration.WilsonCapturedPrimaryFaceWallet

/-! A common physical aperture for every proper subword, with its reference
unit paid before the two regulators at each inactive site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryActiveArms
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonThermometerOwnOffsetField OPE.Cards WilsonCapturedPrimaryFaceWallet
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n k N p : ℕ}
local notation "C" => R.family
local notation "origin" z:max ax:max => WilsonCapturedPrimaryPhysicalArray.registered z (some ax)

structure Shelf (k : ℕ) (d : Fin n → ℕ) (z : Fin n → Site ((C).side N p)) where
  viewer : (i : Fin n) → Sight C (d i) p
  route : (i : Fin n) → Emblems C (d i)
  receipt : WilsonCapturedPrimaryFiledArms.entered R d z (k:=k) viewer route
  blank : (i : Fin n) → Sight C 0 p
  units : (i : Fin n) → Emblems C 0
  reserve : WilsonCapturedPrimaryFiledArms.entered R (fun _ => 0) z (k:=k) blank units

section Given
variable {R} {d : Fin n → ℕ}

def Shelf.eyes {sites : Fin n → Site ((C).side N p)} (S : Shelf (N:=N) (p:=p) R k d sites) (s : Finset (Fin n)) (i : Fin n) : Sight C (level d s i) p :=
  pick (F:=fun e => Sight C e p) (decide (i ∈ s)) (S.viewer i) (S.blank i)

def Shelf.paths {sites : Fin n → Site ((C).side N p)} (S : Shelf (N:=N) (p:=p) R k d sites) (s : Finset (Fin n)) (i : Fin n) : Emblems C (level d s i) :=
  pick (F:=fun e => Emblems C e) (decide (i ∈ s)) (S.route i) (S.units i)

theorem Shelf.used {sites : Fin n → Site ((C).side N p)} (S : Shelf (N:=N) (p:=p) R k d sites) (s : Finset (Fin n)) :
    WilsonCapturedPrimaryFiledArms.entered R (level d s) sites (k:=k) (S.eyes s) (S.paths s) := by
  intro i
  have both (b : Bool) : WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors
      (WilsonThermometerOffsetLedger.cash R) k N p (branch b (d i))
      (WilsonThermometerOffsetResidue.digits R N p (sites i))
      (pick (F:=fun e => Sight C e p) b (S.viewer i) (S.blank i))
      (pick (F:=fun e => Emblems C e) b (S.route i) (S.units i)) := by
    cases b
    · exact S.reserve i
    · exact S.receipt i
  exact both _

theorem limit {D : ℕ} (cap : ∀i,d i ≤ D) (s : Finset (Fin n)) (i : Fin n) : level d s i ≤ D := by
  have both (b : Bool) : branch b (d i) ≤ D := by cases b <;> first | exact Nat.zero_le _ | exact cap i
  exact both _

def Shelf.serves {h u : ℕ} {sites : Fin n → Site ((C).side N p)} (S : Shelf (N:=N) (p:=p) R k d sites)
    (kn : k ≤ N) (un : u ≤ N) (J : ℕ) (door : Opened C h u p) (fee : ℝ) : Prop :=
  ∀ (s : Finset (Fin n)) (x : (i : Fin n) → (C).label (d i)) (y : (i : Fin n) → Palette C (level d s i)),
    WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level d s) (S.paths s) kn (label R s x) y →
    let Y := fun U => ∏ i ∈ s, (C).O N p (x i) (sites i) U
    Booked C N p h Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
      (((∏ i ∈ s, (1+size (y i)))*2^(n-s.card))*fee)
      (WilsonCapturedPrimaryScaledCounter.difference R door un Y)

theorem Shelf.restored {D u h J : ℕ} {sites : Fin n → Site ((C).side N p)} (S : Shelf (N:=N) (p:=p) R k d sites)
    (cap : ∀i,d i ≤ D) (s : Finset (Fin n)) (x : (i : Fin n) → (C).label (d i))
    (y : (i : Fin n) → Palette C (level d s i)) (kn : k ≤ N) (start : (C).ref 0 ≤ N)
    (un : u ≤ N) (door : Opened C h u p) (fee : ℝ)
    (hit : WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level d s) (S.paths s) kn (label R s x) y)
    (budget :
      let a := WilsonCapturedPrimaryFiledArms.arm R (level d s) sites (limit cap s)
        (S.eyes s) (S.paths s) (S.used s) y
      let F := WilsonReflectedPhysicalFiling.reading R a kn
      Booked C N p h F u un ∧ PaidAt (C).S N p J ((C).beta N p) fee
        (WilsonCapturedPrimaryScaledCounter.difference R door un F)) :
    let Y := fun U => ∏ i ∈ s, (C).O N p (x i) (sites i) U
    Booked C N p h Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
      (((∏ i ∈ s, (1 + size (y i)))*2^(n-s.card))*fee)
      (WilsonCapturedPrimaryScaledCounter.difference R door un Y) := by
  have res := WilsonCapturedPrimaryNamedReturn.sale R (level d s) (limit cap s) sites
    (S.eyes s) (S.paths s) (S.used s) kn un door (label R s x) y hit fee budget
  dsimp only at res
  rw [WilsonCapturedPrimaryFaceWallet.field R d s x sites start,
    WilsonCapturedPrimaryFaceWallet.original R d s x sites (S.eyes s) (S.paths s) (S.used s)
      kn start y hit] at res
  exact res

end Given

variable (simple : G.Simple) (book : OPE.Package C R.w (mutt R.alloy.B.a R.Q) R.doors)
include simple in
theorem shelves (shop : RG05Preconstruction.ReadoutPurchase R.b) (d : Fin n → ℕ) :
    ∀ᶠ k : ℕ in atTop, (C).ref 0 ≤ k ∧ ∀ N p, k ≤ N →
      ∀ sites : Fin n → Site ((C).side N p), Nonempty (Shelf (N:=N) (p:=p) R k d sites) := by
  filter_upwards [eventually_ge_atTop ((C).ref 0), WilsonCapturedPrimaryFiledArms.election R d simple shop,
    WilsonCapturedPrimaryFiledArms.election R (fun _ : Fin n => 0) simple shop] with k start old quiet
  refine ⟨start,?_⟩
  intro N p kn sites
  obtain ⟨V,r,moved⟩ := old N p kn sites
  obtain ⟨V0,r0,bought⟩ := quiet N p kn sites
  exact ⟨⟨V,r,moved,V0,r0,bought⟩⟩

variable [NeZero n]

theorem original (hG : G.Simple) (pack : OPE.Package C R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (slow : WilsonWindowReportingPace.Slow R.kit) (D v h J u : ℕ) (wide : 4 < v)
    (enlarged : (C).ref h ≤ J) (station : ∀p, Opened C h u p)
    (tiling : Stock.Tabs.opens (C).path.levels 1 J u) (φ : Test n)
    (d : Fin n → ℕ) (cap : ∀i,d i ≤ D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ radius in trail,
    let m := capture R radius
    let k := launch R hG v radius
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (z : Fin n → Site ((C).side N p)),
      WilsonCenteredCompactBooking.mass R φ radius (N,p) z ≠ 0 → ∀ ax : Fin n,
      ∃ S : Shelf (N:=N) (p:=p) R k d (origin z ax),
        S.serves kn.le (um.trans (m.le_succ.trans (mk.le.trans kn.le))) J (station p) (K*radius^((h:ℝ)+1/32)) := by
  obtain ⟨Z,K,one,_,_,sold⟩ := WilsonCapturedPrimarySpatialFunds.original R hG pack shop slow
    D v h J u wide enlarged station tiling φ
  have grows := (WilsonReflectedPhysicalRate.dates R hG slow v (by omega)).2.grows
  refine ⟨K,one,?_⟩
  filter_upwards [sold, grows.eventually (shelves R hG shop d)] with radius gate stocked
  obtain ⟨um,mk,run⟩ := gate
  refine ⟨um,mk,?_⟩
  intro N p kn z active ax
  obtain ⟨S⟩ := stocked.2 N p kn.le (origin z ax)
  refine ⟨S,?_⟩
  intro s x y hit
  let a := WilsonCapturedPrimaryFiledArms.arm R (level d s) (origin z ax) (limit cap s)
    (S.eyes s) (S.paths s) (S.used s) y
  obtain ⟨_,_,terms,inside,price⟩ := run N p kn z active ax a rfl
  apply S.restored cap s x y kn.le (stocked.1.trans kn.le) _ (station p) _ hit
  exact ⟨terms.works u le_rfl um, tiling.1.trans (um.trans (Nat.le_succ _ |>.trans (mk.le.trans kn.le))), inside, price⟩

end YM.Integration.WilsonCapturedPrimaryActiveArms
