import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildMixedGear
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

variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ}
variable {W:Credit} {n e i r m N:ℕ} {J S:Finset ι}

/-- Lower the input and transfer strips while preserving the complete dated material. -/
def narrow (I:Gear G)(b:ℝ)(h:0<b):Gear G:=
  { I with
    past:=min I.past b
    s:=min I.s b
    σ:=min I.σ (b/2)
    price:=lt_min I.price (half_pos h)
    holds:=lt_min (lt_of_le_of_lt (min_le_left ..) I.holds)
      (lt_of_le_of_lt (min_le_right ..) (half_lt_self h))
    depth:=lt_min I.depth h
    room:=by
      have pos:0<(I.patch.L.val:ℝ):=by exact_mod_cast I.patch.L.pos
      have one:(1:ℝ)≤I.patch.L.val:=by exact_mod_cast I.patch.L.pos
      refine le_min ((div_le_div_of_nonneg_right (min_le_left ..) pos.le).trans I.room) ?_
      apply (div_le_iff₀ pos).mpr
      exact (min_le_right ..).trans (le_mul_of_one_le_right h.le one) }

def stand (I:Gear G)(b:ℝ)(h:0<b)(X:Stand I):Stand (narrow I b h):=
  { X with
    crank:=X.crank.mono le_rfl (min_le_left ..)
    topQ:=X.topQ.mono (min_le_left ..)
    rolls:=X.rolls.mono (min_le_left ..) }

def rally (I:Gear G)(b:ℝ)(h:0<b){i j:ℕ}(X:Rally i j I):Rally i j (narrow I b h):=
  { x:=X.x, σ:=X.σ, rich:=X.rich, θ:=X.θ
    P:=stand I b h X.P
    Q:=stand I b h X.Q
    paid:=fun i j f=>⟨(X.paid i j f).pose.mono (min_le_left ..),
      (X.paid i j f).vale.mono (min_le_left ..),(X.paid i j f).visit.mono (min_le_left ..)⟩
    Υ:=X.Υ.mono (min_le_left ..)
    Χ:=X.Χ.mono (min_le_left ..)
    Ω:=X.Ω.mono (min_le_left ..) }

/-- This cover calculation evaluates the same dated, properly normalized old and fresh polynomials. -/
theorem covered (Q:Realm G (e+1) W)(K:family G D)(eu:Eu k K)(empty:K ∅=0)
    (anchor:Q.anchor ≤ m)(live:m<N)(y:ι → Cover)(z:ι → Site (ll Q.draws m).L)
    (b:ℝ)(hb:0<b)(A:ℝ)(ha:0≤A)
    (wallet:safeB (fun v=> (ll Q.draws m).L.val • y v + lift (z v)) K S e b A)
    (sub:J⊆S)(grade:i≤e):
    let I:=(Q.mint m anchor).gear
    let I':=narrow I b hb
    Wig Bank.terrain y (elixir I')
      (shrinePost G D k e I' * (Q.cash (costXV G e W) m)^muralExp G D k e * A^J.card)
      J ((logO Q.draws Q.paid m N K k J).2 i r):=by
  let I:=(Q.mint m anchor).gear
  let I':=narrow I b hb
  let X:=ReelTime Q (le_refl e) anchor live (le_refl N) (le_refl N)
  let Y:ZL D S e I':=⟨rally I b hb X,K,y,z,A,ha,empty,
    fun J u i hi r=>(wallet J u i hi r).shave (min_le_right ..)⟩
  have P:=((common_scale G D k e).choose_spec I').choose_spec
  by_cases rank:r ≤ mass k J+i
  · rw [onSide Q.draws Q.paid m N K k empty eu Q.hG Q.green live]
    exact P.2 S J sub i r grade rank Y
  · rw [(step_L Q.draws Q.paid m N K k live Q.hG Q.green eu J).coverN i r (by omega)]
    apply Wig.zero.more
    exact mul_nonneg (mul_nonneg P.1 (pow_nonneg (zero_le_one.trans X.rich) _)) (pow_nonneg ha _)

end YM.Integration.WilsonPointChildMixedGear
