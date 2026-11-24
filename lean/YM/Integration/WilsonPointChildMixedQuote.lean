import YM.Integration.WilsonPointChildMixedGear
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildMixedQuote
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open WilsonCoeffUV.Bank.Carp WilsonPointChildPairedHistory
open WilsonPointChildCoveredRead (directions)
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open Borough
open WilsonPointChildFiledSalary (inverseCost)
open WilsonPointChildFiniteRestamp (difference)
open WilsonPointChildCoverStep (routes)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiniteStage (Gap)
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Wheel.Mark WilsonPointChildFiledPress WilsonPointChildWindingSchool
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildPlacedFamily
open WilsonVacuumPreResetMarkedOrdinaryBound (weights)
open private rooted from YM.Integration.WilsonPointChildWindingRoot

open WilsonPointChildPlacedIncome


open WilsonPointChildMixedGear
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι → ℕ} {W:Credit} {e m:ℕ}

/-- The upper course's two stage ordinals fix both original kernel radii. -/
def entry (G:Gauge)(K:KernelChoices)(a b:ℕ):ℝ:=
  if h:4≤a ∧ 5≤b then min (Polestar.splash G K a b h.1 h.2) ((windowBasis G K).width b/2) else 1

theorem entry_pos (K:KernelChoices)(a b:ℕ):0<entry G K a b:=by
  unfold entry
  split
  next h=>exact lt_min (Polestar.spatter G K a b h.1 h.2).1 (half_pos ((windowBasis G K).pos b))
  next _=>exact zero_lt_one

def stages (I:Gear G):Finset ℕ:=Finset.range (I.patch.L.val+3)
theorem populated (I:Gear G):(stages I).Nonempty:=
  ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩

def strip (I:Gear G):ℝ:=min (WilsonPointChildQuoteWidth.quote I)
  ((stages I).inf' (populated I) fun a=> (stages I).inf' (populated I) (entry G I.kernel a))

theorem positive (I:Gear G):0<strip I:=by
  unfold strip
  apply lt_min (WilsonPointChildQuoteWidth.positive I)
  apply (Finset.lt_inf'_iff _).2
  intro a _
  apply (Finset.lt_inf'_iff _).2
  intro b _
  exact entry_pos _ _ _

theorem priced (I:Gear G){a b:ℕ}(ha:a∈stages I)(hb:b∈stages I):
    strip I≤entry G I.kernel a b:=by
  apply (min_le_right ..).trans
  apply (Finset.inf'_le (fun a=> (stages I).inf' (populated I) (entry G I.kernel a)) ha).trans
  exact Finset.inf'_le (entry G I.kernel a) hb

theorem next_strip (Q:Realm G (e+1) W)(h:Q.anchor ≤ m)
    (k₀:Q.draws.clock.J (m+1) ≤ (Q.draws.S.block m).val)
    (rise:5 ≤ Q.draws.clock.J (m+2))
    (stop:(Q.mint (m+1) (by omega)).σ=crestM Q.draws (m+1) rise):
    let I:=(Q.mint m h).gear
    let F:=(Q.mint (m+1) (by omega)).gear
    let u:=(windowBasis G Q.draws.clock.kernel).width (Q.draws.clock.J (m+2))
    strip I ≤ elixir (narrow F u ((windowBasis G _).pos _)):=by
  let I:=(Q.mint m h).gear
  let F:=(Q.mint (m+1) (by omega)).gear
  let u:=(windowBasis G Q.draws.clock.kernel).width (Q.draws.clock.J (m+2))
  have size:I.patch.L.val=(Q.draws.S.block m).val:=rfl
  have slow:Q.draws.clock.J (m+2) ≤ Q.draws.clock.J (m+1)+1:=Q.draws.fits.stepSlow (m+1)
  have ha:Q.draws.clock.J (m+1)∈stages I:=Finset.mem_range.mpr (by omega)
  have hb:Q.draws.clock.J (m+2)∈stages I:=Finset.mem_range.mpr (by omega)
  have price:=priced I ha hb
  have valid:4≤Q.draws.clock.J (m+1) ∧5≤Q.draws.clock.J (m+2):=⟨Q.draws.clock.adm _,rise⟩
  rw [entry,dif_pos valid] at price
  apply price.trans
  have replace:F.σ=crestM Q.draws (m+1) rise:=stop
  have hz:(narrow F u ((windowBasis G _).pos _)).σ=
      min (crestM Q.draws (m+1) rise) (u/2):=congrArg (fun x=>min x (u/2)) replace
  change min (crestM Q.draws (m+1) rise) (u/2) ≤ elixir (narrow F u ((windowBasis G _).pos _))
  rw [←hz]
  exact (pureEl _).le

/-- Enrol the actual reduced upper wallet before either finite side or cutoff is queried. -/
def fare (G:Gauge)(D k:ι → ℕ)(e:ℕ)(I:Gear G):ℝ:=
  max (costXV G e Credit.leanC).x
    ((stages I).sup' (populated I) fun a=>shrinePost G D k e
      (narrow I ((windowBasis G I.kernel).width a) ((windowBasis G I.kernel).pos a)))

theorem post (I:Gear G){a:ℕ}(ha:a∈stages I):
    shrinePost G D k e (narrow I ((windowBasis G I.kernel).width a) ((windowBasis G I.kernel).pos a)) ≤
    fare G D k e I:=by
  apply (Finset.le_sup' (fun a=>shrinePost G D k e
    (narrow I ((windowBasis G I.kernel).width a) ((windowBasis G I.kernel).pos a))) ha).trans
  exact le_max_right ..
end YM.Integration.WilsonPointChildMixedQuote
