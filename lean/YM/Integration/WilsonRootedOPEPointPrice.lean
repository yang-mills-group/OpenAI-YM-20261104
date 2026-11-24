import YM.Integration.WilsonRootedOPEPhysicalMenu
import YM.Integration.ActualOriginalQPointCover
import YM.Integration.ActualOriginalQLayout

/-! At one fixed stage the whole true physical OPE gas has one site price, before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointPrice
open Function Filter Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent MergeProof.Replicums MergeProof.Ribbon
open RG3.Held RG3.Script.Picnic ActualOriginalQReaders
open Extra.Trajectories Push.GridApprox.Nil
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (u : V→MS.Rake.Label B)

local notation "ds" => ActualOriginalQPackets.degree u

def coordinatesAt (L : ℕ) (s : Slot u) : R.family.label s.2.size :=
  (R.family.labels.level s.2.size).scaled (R.family.path.levels.budget L).threshold (coordinates (R:=R) u s)

omit [Nonempty V] [DecidableEq V] in
theorem coverAt (p L : ℕ) (o : V→Site (R.family.side L p)) (a b : V→ℕ) (s : Slot u) :
    let D := ActualOriginalQPointDatum.datum R p L o a b
    coverNumber (R.family.path.levels.budget L).B (ActualRunPhysicalPages.cover R p L (ds s) (ActualOriginalQInput.atomPositions D u) s)≤ActualOriginalQPointCover.bound R u := by
  intro D
  have inside : (R.family.localSection s.2.size).footprint (ActualRunQlocalNativeTuple.root D s.1)⊆ActualOriginalQPackets.plot D u s.1 :=
    fun _ hx=> mem_union_right _ (mem_biUnion.mpr ⟨s.2,mem_univ _,hx⟩)
  change coverNumber _ ((R.family.localSection s.2.size).footprint (ActualRunQlocalNativeTuple.root D s.1)∪ActualOriginalQPackets.plot D u s.1)≤_
  rw [Finset.union_eq_right.mpr inside]
  exact ActualOriginalQPointCover.plot_cover R u p L o a b _ s.1

local notation "C₀" => ((ActualOriginalQPointCover.bound R u:ℕ):ℝ)

theorem purchased (hG : G.Simple) : ∀ᶠ L : ℕ in atTop,∃ c : ℝ,
    ∀ (N p : ℕ) (hL : L≤N) (o : V→Site (R.family.side L p)) (a b : V→ℕ)
      (Q : MS.Land.Prescription B) (μ : ℝ) (orders : V→ℕ),
      let D := ActualOriginalQPointDatum.datum R p L o a b
      let P := R.family.path.rep N p L
      Menu.Arsenal P →
      ∃ f : TestSpace (ActualRunQlocalNativeTuple.orbit D)→Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions D u)→ Menu.Hat (Stock.census V) P,∀ x,
        ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density=GapsLocal.Full.given (f x) 0 ∧
        Menu.Offer (ActualOriginalQPackets.positions D u).origin (f x) (fun _=>1) P.p.B (P.p.supportExponent-4)
          (WilsonRootedOPEPhase.wallet (fun s : Slot u=>readers Q D u μ orders s (x s.1))*(c+c)) := by
  filter_upwards [QLocalPhysicalBirthPurchase.prepaid R (V:=Slot u) hG,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with L granted grown
  let v := coordinatesAt R u L
  let r := QLocalPhysicalBirthPurchase.debit R L 1
  let ρ := r/(1+∑i,QLocalPhysicalBirthWeights.exposure R L (ds) v (C₀) i)
  let h := r+(Real.exp (r+r+R.family.path.levels.clock.forcedAllowance L)-1)
  have age := ActualOriginalQLayout.reference_le R u grown
  have booking := granted (ds) v age (C₀) 1 zero_lt_one
  have positive : 0<ρ := by
    classical
    by_cases nonempty : Nonempty (Slot u)
    · exact booking.1.2.2 nonempty.some
    · letI : IsEmpty (Slot u) := not_nonempty_iff.mp nonempty
      simpa [ρ] using booking.1.1
  let c := WilsonRootedOPEPriceChange.restore (W:=Slot u) ρ*h
  refine ⟨c,?_⟩
  intro N p hL o a b Q μ orders D P stock
  let peaks := ActualOriginalQInput.atomPositions D u
  obtain ⟨sheets,_,_,_,safe⟩ := booking.2 N p hL peaks (fun s=>Nat.cast_le.mpr (coverAt R u p L o a b s))
  have identity : scaledCoordinates (R:=R) (p:=p) (L:=L) u N=v := by
    funext s
    have same : (R.family.path.rep N p L).p=R.family.path.levels.budget L := (R.makes.wilson.represents N p L hL).vac
    unfold scaledCoordinates
    rw [same]
    rfl
  let prices := ActualRunFullPages.prices R p L peaks (ds) v sheets
  have trueRaw : MenuSafe (ActualOriginalQInput.atomPages D u hG N hL) peaks prices (fun _=>ρ) h := by
    unfold ActualOriginalQInput.atomPages
    rw [identity]
    exact safe
  exact WilsonRootedOPEPhysicalMenu.original Q D u μ orders hG N hL prices c
    (WilsonRootedOPEPriceChange.restored _ _ _ ρ positive trueRaw) stock

end YM.Integration.WilsonRootedOPEPointPrice
