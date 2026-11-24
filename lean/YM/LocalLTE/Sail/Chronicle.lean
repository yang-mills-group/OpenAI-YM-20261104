import YM.LocalLTE.XPane.Actuary
/-!
# The column stencil program, with explicit prophecy names

Prophecies pinned PRIOR to further passing events (not from arbitrary
subsequent inhabited compilation results, which could change choices).
Preserves the literal Moment stencils. Exposes ranked appointments for shared
launch consumers, without redefining ANY history objects or cone guarantees.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool
structure Almanac where
    atlas : GuideF
    demand : GuideF
    outfit : GuideF
    order : Gazette demand outfit
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{E:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}{R:Register D E w v} {m l q r p N:ℕ}{κ e:ℝ} {V:Delays T}
structure Chronicles {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{E:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}
    (R:Register D E w v)(m:ℕ)(κ:ℝ)(q l r p N:ℕ)(e:ℝ) (V:Delays T) (A:Almanac):Prop where
    provision : Series (X:=X) R m κ q l r p N e V
    readings : ∀ i j,StepStages i j→∀ n≤N,∀ x:ℝ,V.betaEntry i≤x→ LocalLTE.Fan.ManifestC (C i j) (D.L i) (R.o i j) (E i j) Push.SectorMeasure.Chi.canonical (X.p.profile j).order (X.p.profile j).power m q l (A.demand i j n) (A.atlas i j n) (A.outfit i j n) κ e Mallow.aust x (R.μ i j)
lemma Chronicles.names (h:Series (X:=X) R m κ q l r p N e V):∃ A,Chronicles (X:=X) R m κ q l r p N e V A:=by
    obtain ⟨u,a,f,hX,hP⟩:=h.periods; exact ⟨⟨u,a,f,hX⟩,h,hP⟩
variable {A:Almanac} {Y:Delays T}
lemma Chronicles.rightward (h:Chronicles (X:=X) R m κ q l r p N e V A)(ht:DelayLe V Y): Chronicles (X:=X) R m κ q l r p N e Y A:=by
    have hU(i j:ℕ)(he:StepStages i j)(n:ℕ)(hP:n≤N)(x:ℝ)(hY:Y.betaEntry i≤x):= h.readings i j he n hP x ((ht.beta _).trans hY)
    let Z:=h.provision; refine ⟨⟨(Z.columns.trans (ht.shells 0)),fun i=> (Z.plume i).trans (ht.shells i), fun i=>(Z.grew i).trans (ht.growth i),⟨A.atlas,A.demand,A.outfit,A.order,hU⟩,fun i j he x hp=> Z.limits _ _ he _ ((ht.beta _).trans hp)⟩, hU⟩
end YM.PhysicalNext.Repeat.Legato.Spiral
