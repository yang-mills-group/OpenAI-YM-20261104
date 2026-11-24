import YM.Integration.WilsonReporterWeightedReturn
import YM.TraceExtension.Prom.Front.West.Tael

/-! The expanded source is issued on the original N-born course. Only the
diagonal Wick comparison on its attained normal chart is left to the caller. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedDeployment
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open Function Source Extra.Histories MergeProof.Accent PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {N k p m D u : ℕ} {w r l z : ℝ} {ξ : Purse}
    (B : Binding C) (H : C.Makes) {O : HaarBudget G} (J : ChartRatio G)
    {W : Bid.Worth} {u₀ ψ φ δ : ℕ → ℝ} {rad : ℕ → ℕ}
    {door : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (scrim : Scrim C W u₀ ψ φ δ (fly C.path.levels) rad door)
    {x : Points (m+1)} {d : Fin (m+1) → ℕ} {P : (i : ℕ) → Rep G (C.side i p)}
set_option quotPrecheck false
local notation "AX" => C.path.levels
local notation "α" => stamp AX N p
local notation "Y" => clim AX k

include scrim in
theorem original (L : LegacyCostSky B J w z ξ k u D O l r) (hN : k<N)
    (V : WhipSky B J ξ L.hours L.moves (isohypse H hN.le p) P (widthSky AX ξ.band k) le_rfl)
    (ht : 0≤ξ.band) (bank : Ship.bank O AX (widthSky AX ξ.band k))
    (hh : ∀ A : BudgetPoint, A.B ≤ walls Y → Tickets A (kinetics Y))
    (refs : ∀ i, C.ref (d i)≤k)
    (F : (i : Fin (m+1)) → Ribbon.StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q α)
    (g t : (i : Fin (m+1)) → C.label (d i)) (place : FitSky AX ξ.band k x)
    (u₂ : 2≤u) (names : m+1≤u)
    (spaced : Spaced (scouts C k) (seatsSky C ξ.band x hN.le p))
    (cash : ∀ i, ξ.cash Y*moneys C (d i) k N p (t i) ≤ Perch.bill (-8) Y)
    (coins : ∀ i, Rise.coin ((F i).W (t i)) ≤ ξ.principal Y)
    (hard : ∀ i, Hat Y^z * paid C (d i) k N p (t i) ≤ fly AX (d i) k)
    (target : Peak.sufficientlySky C (Atlas.jointX g) ξ.band x k)
    (calibrated : WilsonReporterWeightedReturn.Signed g t place F)
    (face : Glyph.modes (Fin (m+1))) (occupied : face.val.Nonempty) :
    (Ship.yardSky C ξ.band hN.le p).rootTest (C.beta N p) (fun U =>
      (Ship.invoiceSky (Atlas.jointX g) (Edition.q_asked (C:=C) t) place N p U).part face) ≤ Ship.budget AX u k := by
  let course := isohypse H hN.le p
  have nylon := embroideredSky B J course ξ H L.hours L.token L.moves P V ht
  have ceremony := v_ceremonySky nylon L.moves.coup
  have room := L.room _ names
  have passing := billing_XSky B J H L.hours P L.moves V x place nylon room hh (L.tariff _ names)
  let Q := C.path.rep N p k
  let sites := seatsSky C ξ.band x hN.le p
  have sp : Edition.Spaced Q.p.B sites := by
    rw [show Q.p=C.path.levels.budget k from (H.wilson.represents N p k hN.le).vac]
    exact spaced
  have rad_pos : 0 < Hat Y ^ z := Real.rpow_pos_of_pos
    (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed _)))) _
  have stock := caughtXSky C N k p m t ξ.band x hN H refs course scrim.1
    ⟨fun _ _ i hi j hj hij => sp i j hij⟩
    (fun a => (Extra.Multi.Occupancy.of_injective (injected _ sites Q.p.B_pos sp) a).trans (scrim.2 k))
    rad_pos hard
  have filed := attireSky x t F H refs ceremony L.moves V.stops room passing u₂ place spaced cash coins stock
  exact WilsonReporterWeightedReturn.original g t L.age bank names nylon place target passing F calibrated filed face occupied

end YM.Integration.WilsonReporterWeightedDeployment
