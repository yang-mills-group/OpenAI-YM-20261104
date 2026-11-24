import YM.Integration.WilsonPositionProgramOrderedCaptureTensor
import YM.Integration.WilsonPositionProgramNominatedPin

/-! Choose the truncated microscopic history at a fixed report and tolerance.
The same submitted field, proper mask and profile are used in both programs.
Their two top cutoffs may be chosen after the bound. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramOrderedPinReturn
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

open WilsonMarkedIndependentNormalizedElection (deck normalized)



private theorem moved (X:Era G Lounge)(o:CellR)(b:Cover)(t r:ℕ):
    (locale o (shifted X b)).2 t r = WilsonCoeffUV.Soil.revolve b ((locale o X).2 t r) := by
  funext w
  rfl

private theorem moved_sub {α:Type*} {r:ℕ} (x y:(Fin r → Cover × α) → ℝ)(root:Cover):
    WilsonCoeffUV.Soil.revolve root (x-y) =
      WilsonCoeffUV.Soil.revolve root x - WilsonCoeffUV.Soil.revolve root y := by
  funext w
  rfl

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∃c wallet:Credit,∀ᶠ j:ℕ in atTop,∀m:ℕ, j ≤ m → ∀F ε:ℝ, 0 ≤ F → 0 < ε →
    ∃K:ℕ,m ≤ K ∧ F * trailC L.S m K < ε ∧
    ∀N M:ℕ,K ≤ N → K ≤ M → ∀X:Herit Q,
    ∀b:ℕ,j ≤ b → b ≤ m → ∀(φ:Wilt Q)(B:Fin (a+1)→ℝ)(y Z:ℝ)(o:CellR)(root:Cover),
    Compar L.S (zz L) b m ≤ Z → Bough Q φ y Z B →
    c.buy Z * ∏i,B i*(wallet.buy (zz L m)*WilsonPositionProgramNormalizedMaster.fee X e i) ≤ F →
    let read:=fun n=>locale o (cruises L R.metals.O n (capP Q) n b (shifted
      (HearthC Q L R.metals.O φ (normalized L R.metals.O Q X m n) m n n y)
      (WilsonPositionProgramPinnedHearthHistory.pin L.S b n root)))
    ∀t r:ℕ,t ≤ e →
      YieldP root 1 u F (trailC L.S m K) ((read N).2 t r) ((read M).2 t r) ∧
      Fruit root 1 u ((read N).2 t r-(read M).2 t r) ε := by
  intro Q L
  obtain ⟨c,w,cohort⟩:=WilsonPositionProgramOrderedCaptureTensor.original R simple v paid
    big rails l d fit cap
  refine ⟨c,w,?_⟩
  filter_upwards [cohort,WilsonPositionProgramNominatedPin.original R simple v paid big rails l d fit cap]
    with j settled pinned
  intro m late F ε pos tol
  obtain ⟨K,stop,small,all⟩:=settled m late F ε pos tol
  refine ⟨K,stop,small,?_⟩
  intro N M fine fine' X b awake earlier φ B y Z o root room shape price
  have hN:=pinned m N b late (stop.trans fine) (earlier.trans (stop.trans fine)) X φ y root
  have hM:=pinned m M b late (stop.trans fine') (earlier.trans (stop.trans fine')) X φ y root
  dsimp only
  rw [hN,hM]
  intro t r grade
  have p:=(all N M fine fine' X b awake earlier φ B y Z o room shape price).heapS t r grade
  have h:YieldP root 1 u F (trailC L.S m K)
    ((locale o (shifted (LodeStar L R.metals.O φ (normalized L R.metals.O Q X m N) m b N y) root)).2 t r)
    ((locale o (shifted (LodeStar L R.metals.O φ (normalized L R.metals.O Q X m M) m b M y) root)).2 t r):=by
    rw [moved,moved]
    constructor
    · simpa only [add_zero] using p.wax.turn root
    · simpa only [add_zero] using p.wane.turn root
    · rw [← moved_sub]
      simpa only [add_zero] using p.toll.turn root
  exact ⟨h,Award.more h.toll small.le⟩

end YM.Integration.WilsonPositionProgramOrderedPinReturn
end
