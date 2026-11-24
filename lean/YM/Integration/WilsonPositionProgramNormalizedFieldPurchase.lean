import YM.Integration.WilsonPositionProgramFieldSeriesCost

/-! Actual reannounced cutoff doses in the independently normalized window.
Both polynomial receipts are posted before accuracy tests, cutoff and period.
The spatial probe at each child keeps its original angular test. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramNormalizedFieldPurchase
open Function Finset Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels PowerSeries
open WilsonPositionProgramInversionMaterial
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {a h D k u e : ℕ}

theorem original (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ C B : Fin (a+1) → Credit, ∀ᶠ j : ℕ in atTop, ∀ (m M : ℕ), j ≤ m → m ≤ M →
      ∀ (X : Herit Q) (b : (s : Fin (a+1)) → Volume (d s)),
      let x := fun i => PermuteLens L R.metals.O (Q i) M m (X i)
      let w := fun i => steep L R.metals.O (Q i).ans (Q i).path M m (M-m) (x i)
      let f := fun i => (C i).buy (Compar L.S (zz L) m M) *
        ((B i).buy (zz L m)*WilsonPositionProgramNormalizedMaster.fee X e i)
      ∀ a' : Axes R l, ∀ t≤e, ‖coeff t (dose R l w d admit b a')‖ ≤
        ((e+1:ℕ):ℝ)^Fintype.card (Fin (a+1)) *
          ∏ i, f i * ‖jewelBloom (admit i) (a' i) (b i)‖ := by
  intro Q L
  obtain ⟨C,B,paid⟩ := WilsonPositionProgramDatedFieldCost.original R simple v funded p rails l d admit cap
  refine ⟨C,B,?_⟩
  filter_upwards [paid] with j sales
  intro m M jm mM X b x w f a' t ht
  have entries := sales m M jm mM X
  have fee (i s t) (ht : t≤e) : ‖coeff t (w i s)‖ ≤ f i := entries i t ht s
  have pos i : 0≤f i := (norm_nonneg _).trans (fee i (a' i) 0 (Nat.zero_le _))
  exact WilsonPositionProgramFieldSeriesCost.native R l d admit w b e f pos (fun i t ht s => fee i s t ht) a' t ht

end YM.Integration.WilsonPositionProgramNormalizedFieldPurchase
end
