import YM.Integration.WilsonPositionProgramLocatedMaster
import YM.Integration.WilsonPositionProgramDatedFieldCost

/-! The submitted upper field is a finite sum of the actual separately
translated children at each real residue. Its complete enrolled pulse returns
on every intervening original single-source block. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramLocatedFieldCourse
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext.Repeat.Legato Labels Source Source.Drops
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Blue
open WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {a h D k u e : ℕ}
local notation "L" => R.family.path.levels

theorem original (simple : G.Simple) (fund : ℕ → Gear G → ℝ)
    (prepaid : FundedMarkedCoverRows.prices fund R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (fit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d fit) ≤ k) :
    let Q := deck (G:=G) l d fit
    ∀ᶠ f : ℕ in atTop, ∀ m M, f ≤ m → m ≤ M → ∀ (X : Herit Q) i (φ : Rarity (d i)) (y : ℝ),
      let x := PermuteLens L R.metals.O (Q i) M m (X i)
      let v := steep L R.metals.O (Q i).ans (Q i).path M m (M-m) x
      let Y := centralL L R.metals.O M m M (Q i) x
      let t := paceT (L).S m M
      let launch := fun j => (Q i).spins L R.metals.O φ m j M y x
      (∀ c : CellR, locale c (launch M) =
        ∑ z∈VisitsT φ t y c, drumB (l i) t • locale c (shoe Y φ t y z)) ∧
      (∀ (c : CellR) (z : Cover) (n : Side),
        let b := wheelC t y z φ.ψ c
        let H := WilsonPositionProgramMasterBirth.rank R (d:=l i)
        (PowerSeries.X : Ink (Woods G n))^H * flash ((locale c (shoe Y φ t y z)).1 n) =
          loom (spear (jog (wrap n z) : Woods G n ≃ Woods G n))
            (∑ s, (PowerSeries.X : Ink (Woods G n))^(H-valence (Q i).F s) * Blue.soil (v s) *
              (jewelBloom (fit i) s b • jet (Plies (Q i).ans (sheet (Q i).F s) n)))) ∧
      ∀ j, m ≤ j → j < M → verseI L R.metals.O j M (l i) (launch (j+1)) = launch j := by
  intro Q
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple fund prepaid p rails l d fit cap]
    with f filed
  obtain ⟨Z,W,levels,ratio,calendar,first,_,_,_,frames,_⟩ := filed
  intro m M fm mM X i φ y x v Y t launch
  obtain ⟨stamp⟩ := frames i
  let A := stamp.p.f.arch
  have lv : A.V.draws=L := stamp.p.lands.trans levels
  have rt : A.V.paid=R.metals.O := stamp.p.modes.trans ratio
  have m₀ : A.V.anchor ≤ m := (stamp.p.tap.trans first).symm ▸ fm
  have enrolled := tournure (m:=m) A x (m₀.trans mM) (le_refl M)
  rw [lv,rt] at enrolled
  refine ⟨fun c => pupil_eye (l i) Y φ t y c (pace_pos ..),?_,?_⟩
  · intro c z n
    exact WilsonPositionProgramLocatedMaster.root R (fit i) m M n t y z c φ (X i) enrolled
  · intro j mj jM
    have step := priceReset A φ x y m₀ mj jM
    dsimp only at step
    rwa [lv,rt] at step

end YM.Integration.WilsonPositionProgramLocatedFieldCourse
end
