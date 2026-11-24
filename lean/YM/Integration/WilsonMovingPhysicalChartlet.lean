import YM.Integration.WilsonMovingLogPaid
import YM.Integration.WilsonMovingSensorTrueField

/-! Actual geometry and measured coupling of a represented station inside the
original catalogue. All five independent catalogue sensors have the same
measured coupling but their own genuine parent period and charts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingPhysicalChartlet
open Function Filter Lattice RG Pressure Pressure.Testing Wilson Input Org
open Push Push.AbsoluteSums Push.Uniform Push.PriceCompiler Precision
open PhysicalNext PhysicalNext.Repeat Legato Boulevard Roost Sienna Pane Lapis
open Tree Further.PhysicalPeriodLimitF933.Mural Planned.JetPort AnalyticBridge VerifiedReset Collection Quotes RG.Shoot
open Juniper Juniper.Bright Juniper.Mulberry ConnectedActivityE6 Coat
open Push.SectorMeasure Fare Gauge Blaze Brush ThroughLaunch
open scoped Topology Classical
variable {G:Gauge} (R:Run G)

/-- The physical commissioning band at the exact upper age. -/
theorem band {N per m:ℕ}(live:m<N) :
    R.family.path.β N per (m+1)∈ Rain.lands R.alloy m :=
  (R.makes.wilson.represents N per (m+1) live).band

/-- An original represented torus in the numerical catalogue range owns an
actual Cash and a Quilt for every submitted forest on that very torus. -/
theorem measured {N per m:ℕ}(live:m<N)
    (lower:100*(1+(R.family.path.levels.budget m).B)≤(R.family.side m per).val)
    (upper:(R.family.side m per).val≤Trio.most (Bright.miner R.kit m) (R.alloy.B.a.clock.hatBeta m)) :
    let x:=R.alloy.B.a.clock.hatBeta m
    let I:=R.alloy.B.a.clock.J m
    let J:=R.alloy.B.a.clock.J (m+1)
    let H:=Lattice.Ratio.exact_size (R.alloy.B.a.S.oneStep m per)
    let T:=WilsonVacuumPreResetColdInput.tube R N per m
    let Y:=Pane.virgin T (R.family.path.levels.budget (m+1)) (R.family.path.β N per (m+1))
    ∃ V:Chartlet R.kit.shape R.alloy N m H Y, SeekR R.kit.shape R.alloy N m H V ∧
      ∀ F:Forest (Pane.panel R.alloy m H).ratio, Quilt T F (widest R.rolls R.kit.target J I x) := by
  intro x I J H T Y
  obtain ⟨V,hV⟩:=Bright.reception R.kit H live (band R live) lower
  exact ⟨V,hV,fun F=>Trio.quilt G (R.rolls.L J) (Bright.miner R.kit m) x
    (Pane.panel R.alloy m H) T F upper V.laws.data.funds.length_eq V.laws.data.room.larger⟩

/-- The original finite catalogue at the genuinely measured physical beta
retains its five distinct torus charts and each full forest size. -/
theorem sensors {N per m:ℕ}(live:m<N) :
    let x:=R.alloy.B.a.clock.hatBeta m
    let I:=R.alloy.B.a.clock.J m
    let J:=R.alloy.B.a.clock.J (m+1)
    let β:=R.family.path.β N per (m+1)
    ∃ W:Bright.Guidebook R.kit N m β, ∀ i:Slide.Stars,
      SeekR R.kit.shape R.alloy N m (Bright.sews R.kit m i) (W.pages i) ∧
      (radiusB x≤(Bright.caves R.kit m i).val) ∧
      ∀ F:Forest (Pane.panel R.alloy m (Bright.sews R.kit m i)).ratio,
        Quilt (Pane.orchestra R.alloy N (Bright.sews R.kit m i)) F (widest R.rolls R.kit.target J I x) := by
  intro x I J β
  obtain ⟨W⟩:=Bright.resident R.kit live (band (per:=per) R live)
  exact ⟨W,fun i=>⟨W.sells i,WilsonMovingSensorTrueField.fence x (Bright.miner R.kit m) i,
    fun F=>Gauze.ahead R.kit W i F⟩⟩

end YM.Integration.WilsonMovingPhysicalChartlet
end
