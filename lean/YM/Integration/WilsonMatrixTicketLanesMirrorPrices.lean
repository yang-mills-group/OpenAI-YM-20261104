import YM.Integration.WilsonMatrixTicketLanesMatchedProfiles
import YM.Integration.WilsonMatrixTicketLanesMirrorFabric

/-! Exact finite marked perturbative prices on the original physical block calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesMirrorPrices
open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Local.Physical MS.Menus MS.Book.Program
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge}

/-- The complete open-forest formal coefficient agrees with the independently priced mixed roster. -/
theorem read {n : Side} {L : Fabric G n} (E : Exhibit L) (paid : Long L)
    (V : Warehouse G) (article : CapReady.Article V L E paid) (even : Even n.val)
    {W : Type} [LinearOrder W] (B : Deck G) (s : Finset W) (d : W → ℕ)
    (x : W → Lattice.Cover) (a : Lattice.Cover) (t : Team) (r : ℝ)
    (A : (i : W) → Acts B (d i)) :
    Score.netE (tagPrice E d x s A t r V a) =
      Score.netE (Track.ticketRead V n d t r A a x s) :=
  (article.voices W s B d x a t r A _).mp
    ((Track.finite_bridge V even d A t r a x s _).mpr rfl)

/-- All actual original periods and histories, before the finite roster or perturbative order is requested. -/
theorem original (R : Run G) : ∀ᶠ b : ℕ in atTop, ∀ (p k : ℕ)
    (σ : Picks R.family.path p),
    let H := R.family.path
    let L := segment H p b σ k
    ∃ (paid : Long L) (E : Exhibit L), E.chart = R.metals.O ∧
      (∀ j, rates E.quotes k j = Delay.stones (offset H p b k) j) ∧
      (∀ (V : Warehouse G), CapReady.Article V L E paid) ∧
      ∀ {W : Type} [LinearOrder W] (B : Deck G) (s : Finset W) (d : W → ℕ)
        (x : W → Lattice.Cover) (a : Lattice.Cover) (t : Team) (r : ℝ)
        (A : (i : W) → Acts B (d i)),
        let V := WilsonMatrixTicketLanesNativePrices.warehouse R
        Score.netE (tagPrice E d x s A t r V a) =
          Score.netE (Track.ticketRead V (R.family.side (b+k) p) d t r A a x s) := by
  filter_upwards [WilsonMatrixTicketLanesMirrorFabric.original R] with b hb p k σ
  obtain ⟨paid,E,chart,_,clock,article⟩ := hb p k σ
  refine ⟨paid,E,chart,clock,article,?_⟩
  intro W _ B s d x a t r A
  have he : Even (R.family.path.S.side (b+k) p).val := by
    obtain ⟨m,hm⟩ := R.family.path.S.side_four (b+k) p
    exact ⟨2*m, by omega⟩
  exact read E paid _ (article _) he B s d x a t r A


end YM.Integration.WilsonMatrixTicketLanesMirrorPrices
