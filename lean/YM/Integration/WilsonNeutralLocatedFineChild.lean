import YM.Integration.WilsonOriginalPrimerFiledPages
import YM.Integration.WilsonNeutralDisplacedAngular

/-! The independently filed location is the parent and residue of the
same fine position on the original torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralLocatedFineChild
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical



open WilsonOriginalPrimerFiledPages
open WilsonRunFormalMarkedStep

theorem ports {c f:Side}(q:Ratio c f)(y:Site c)(x:Site q.count):
    let w:=sites (q.assemble (y,x)) (c*q.count)
    let p:Ratio c (c*q.count):=Ratio.mk q.count rfl
    p.parent w=y ∧ p.residue w=x:=by
  cases q with
  | mk L equal =>
    have sides:f=c*L:=Subtype.ext equal
    subst f
    simp [sites,Ratio.assemble_parent]

theorem original {G:Gauge}(R:Run G)(N i per:ℕ)(y:Site (R.family.side i per))
    (x:Site (R.family.path.levels.S.block i)):
    let c:=R.family.side i per
    let q:=(R.family.path.levels.clock.op i per).ratio
    let L:=(destination R.family.path.levels N i).L
    let p:Ratio c (c*L):=Ratio.mk L rfl
    let w:=sites (q.assemble (y,x)) (c*L)
    p.parent w=y ∧ p.residue w=x:=by
  exact ports (R.family.path.levels.clock.op i per).ratio y x

end YM.Integration.WilsonNeutralLocatedFineChild
end
