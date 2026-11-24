import YM.Integration.WilsonPositionProgramInvertedCohort

/-! Literal representation of the entire finite joint child material on the
one normalized inversion. The retested window and the child coordinates
are funded on the original hierarchy before either physical regulator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramFiniteRootMaterial
open Set Function Filter Finset Matrix PowerSeries Lattice Wilson RG RG.Supply Next.Foundations
open PhysicalNext.Repeat.Legato Source Precision XSpace Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Blue
open WilsonPositionProgramInversionMaterial WilsonPositionProgramInvertedStencil
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {a h D k u e : ℕ}
local notation "G₀" => R.family.path.levels

def field (l d : Fin (a+1) → ℕ) (fit : ∀ i,l i < d i) (m M : ℕ)
    (X : Herit (deck (G:=G) l d fit)) (i : Fin (a+1)) :
    Verse (R.family.labels.level (l i)) :=
  let Q := deck (G:=G) l d fit
  let x := PermuteLens G₀ R.metals.O (Q i) M m (X i)
  steep G₀ R.metals.O (Q i).ans (Q i).path M m (M-m) x

def bill (d : Fin (a+1)→ℕ) (m M : ℕ) (φ : (i:Fin (a+1))→ Rarity (d i))
    (y : Fin (a+1)→ℝ) (z : Fin (a+1)→ Cover) (c : Fin (a+1)→ CellR) (i : Fin (a+1)) : Volume (d i) :=
  wheelC (paceT R.family.S m M) (y i) (z i) (φ i).ψ (c i)

def entered (l d : Fin (a+1) → ℕ) (fit : ∀ i,l i < d i) (m M : ℕ)
    (X : Herit (deck (G:=G) l d fit)) (φ : (i:Fin (a+1))→ Rarity (d i))
    (y : Fin (a+1)→ℝ) (z : Fin (a+1)→ Cover) (c : Fin (a+1)→ CellR)
    {P : Period} (T : P.Tree) : Bare.Series T G :=
  let Q := deck (G:=G) l d fit
  let voter := fun i => PermuteLens G₀ R.metals.O (Q i) M m (X i)
  let Y := fun i => centralL G₀ R.metals.O M m M (Q i) (voter i)
  let t := paceT R.family.S m M
  packet T ((PowerSeries.X:Ink (Woods G P.side))^ceiling R l *
    ∏ i, flash ((locale (c i) (shoe (Y i) (φ i) t (y i) (z i))).1 P.side))

theorem original (simple : G.Simple) (fund : ℕ → Gear G → ℝ)
    (prepaid : FundedMarkedCoverRows.prices fund R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (fit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d fit) ≤ k) :
    let Q := deck (G:=G) l d fit
    ∀ᶠ f : ℕ in atTop, ∀ m M, f ≤ m → m ≤ M →
      ∀ (X : Herit Q) (φ : (i:Fin (a+1))→ Rarity (d i)) (y : Fin (a+1)→ℝ)
        (z : Fin (a+1)→ Cover) (c : Fin (a+1)→ CellR) (P : Period) (T : P.Tree),
      entered R l d fit m M X φ y z c T =
        finite R P l z T (dose R l (field R l d fit m M X) d fit (bill R d m M φ y z c)) := by
  intro Q
  filter_upwards [WilsonPositionProgramLocatedFieldCourse.original R simple fund prepaid p rails l d fit cap]
    with f sale
  intro m M fm mM X φ y z c P T
  let x := fun i => PermuteLens G₀ R.metals.O (Q i) M m (X i)
  let Y := fun i => centralL G₀ R.metals.O M m M (Q i) (x i)
  let temp := paceT R.family.S m M
  let root := fun i => flash ((locale (c i) (shoe (Y i) (φ i) temp (y i) (z i))).1 P.side)
  exact WilsonPositionProgramInvertedCohort.assembled R T l d fit z
    (field R l d fit m M X) (bill R d m M φ y z c) root
    (fun i => (sale m M fm mM X i (φ i) (y i)).2.1 (c i) (z i) P.side)

end YM.Integration.WilsonPositionProgramFiniteRootMaterial
end
