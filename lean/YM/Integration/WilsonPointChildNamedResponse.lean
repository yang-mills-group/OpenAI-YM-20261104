import YM.Integration.WilsonPointChildMixedSalary
import YM.Integration.WilsonPointChildNamedPortfolio
import YM.Integration.WilsonPointChildMixedQuote
import YM.Integration.WilsonPointChildReceivedFace
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNamedResponse
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

open WilsonPointChildMixedQuote WilsonPointChildReceivedFace
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι → ℕ} {E m N:ℕ} {S:Finset ι}

open WilsonPointChildMixedSalary
open WilsonCoeffUV.Wheel.Address

def output (L:Levels G)(O:ChartRatio G)(m N:ℕ)(k:ι  →  ℕ)(T:Finset ι)
    (α β:(ι  →  Cover) → family G D)(y:ι  →  Cover)(z:ι  →  Site (ll L m).L)(z':ι  →  Site (ll L (m+1)).L):family G D:=
  let g:=chartIn (ll L m) y z
  let old:=logO L O (m+1) N (α (chartIn (ll L (m+1)) g z')) k
  logO L O m N (mounted T old (β g)) k

def salary (Q:Realm G (E+1) Credit.leanC)(m:ℕ)(hq:Q.anchor ≤ m)(k D:ι  →  ℕ)(A B:ℝ)(I:Finset ι):ℝ:=
  let F:=(Q.mint m hq).gear
  let I':=narrow F (strip F) (positive F)
  shrinePost G D k E I'*(Q.cash (costXV G E Credit.leanC) m)^muralExp G D k E *
    ((Q.y (m+1))^bill G D k E*A+B)^I.card

theorem covered (Q:Realm G (E+1) Credit.leanC)(h:Q.anchor  ≤  m)(live:m+1<N)
    (k₀:Q.draws.clock.J (m+1)  ≤  (Q.draws.S.block m).val)
    (k₁:Q.draws.clock.J (m+2)  ≤  (Q.draws.S.block (m+1)).val)
    (rise:5  ≤  Q.draws.clock.J (m+2))
    (stop:(Q.mint (m+1) (by omega)).σ=crestM Q.draws (m+1) rise)
    (cash:fare G D k E (Q.mint (m+1) (by omega)).gear  ≤  Q.cash Credit.leanC (m+1))
    (T I:Finset ι)(α β:(ι → Cover) → family G D)
    (ea:∀x,Eu k (α x) ∧ α x ∅=0)(eb:∀x,Eu k (β x))
    (A B:ℝ)(pa:0 ≤ A)(pb:0 ≤ B)
    (a:∀x,safeB x (α x) I E ((windowBasis G Q.draws.clock.kernel).width (Q.draws.clock.J (m+2))) A)
    (b:∀x,safeB x (β x) I E (strip (Q.mint m h).gear) B)
    (e r:ℕ)(he:e ≤ E)(y:ι → Cover)(z:ι → Site (ll Q.draws m).L)(z':ι → Site (ll Q.draws (m+1)).L):
    let F:=(Q.mint m h).gear
    let w:=elixir (narrow F (strip F) (positive F))
    Wig terrain y w (salary Q m h k D A B I) I ((output Q.draws Q.paid m N k T α β y z z' I).2 e r):=by
  intro F w
  let g:=chartIn (ll Q.draws m) y z
  let x:=chartIn (ll Q.draws (m+1)) g z'
  let old:=logO Q.draws Q.paid (m+1) N (α x) k
  have oldFee:=prior Q h live k₀ k₁ rise stop cash (α x) (ea x).1 (ea x).2 g z' A pa (a x)
  have yp:0 ≤ Q.y (m+1):=zero_le_one.trans (Q.depth _ (by omega))
  have both:=combine g T old (β g) (mul_nonneg (pow_nonneg yp _) pa) pb oldFee (b g)
  have eu:Eu k old:=fun J=>step_L Q.draws Q.paid (m+1) N (α x) k live Q.hG Q.green (ea x).1 J
  have emp:old ∅=0:=logHush ..
  obtain ⟨valid,quiet⟩:=WilsonPointChildReceivedFace.legal T eu (eb g) emp
  exact WilsonPointChildMixedGear.covered Q (mounted T old (β g)) valid quiet h (by omega) y z
    (strip F) (positive F) _ (add_nonneg (mul_nonneg (pow_nonneg yp _) pa) pb) both (Subset.rfl) he

end YM.Integration.WilsonPointChildNamedResponse
