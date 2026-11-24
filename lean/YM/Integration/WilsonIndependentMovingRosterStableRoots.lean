import YM.Integration.WilsonSeparatedPrefixMovingLenses
import YM.Integration.WilsonIndependentMatchedRosterFronts

/-! Pairwise geometric income for a signed stable mask with one exterior
source on its own mesh and any number of sources on the finer report. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableRoots

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

variable {n h:ℕ}{D:Fin (n+1)→ℕ}

def front (P:Patch)(φ:(i:Fin (n+1))→Rarity (D i))(ψ:Rarity h)(x y T:ℝ)(o:CellR):
    Fin ((n+1)+1)→ProfileW:=
  Fin.cons (saddleP P.L (VisitsT ψ (x/T) (y/T) o))
    (fun i=>saddleP P.L (VisitsT (φ i) x y o))

private theorem reverse {p q:ProfileW}{η w d:ℝ}(a:SplitHill p q η w d):SplitHill q p η w d:=by
  refine ⟨a.lipQ,a.lipP,a.globe,a.toll,a.nonneg,a.year,a.rate,a.edge,?_⟩
  intro u v
  have b:=a.gap v u
  rw [Bank.terrain.swap v u] at b
  linarith

theorem original (P:Patch)(φ:(i:Fin (n+1))→Rarity (D i))(ψ:Rarity h)(x y T gap zNear zFar:ℝ)
    (o:CellR)(positive:0<x)(zoom:1≤T)(fit:x*P.L.val≤1)(distanced:0<gap)
    (same:∀i j,i≠j→ClearDay (φ i) (φ j) gap)
    (different:∀i,∀a∈tsupport (φ i).ψ.val,∀b∈tsupport ψ.ψ.val,gap≤dist a (T • b))
    (nearBox:∀i,radiusH (φ i) (x*P.L.val) y≤zNear)
    (farBox:radiusH ψ ((x/T)*P.L.val) (y/T)≤zFar)
    (nearLive:∀i,(VisitsT (φ i) x y o).Nonempty)(farLive:(VisitsT ψ (x/T) (y/T) o).Nonempty):
    let f:=front P φ ψ x y T o
    ∀a b,a≠b→SplitHill (f a) (f b) (x*P.L.val) (4*max zNear (T*zFar)) (gap/(x*P.L.val)):=by
  intro f
  have cross (i:Fin (n+1)):=WilsonSeparatedPrefixMovingLenses.original P (φ i) ψ x y T gap zNear zFar o
    positive zoom fit distanced (different i) (nearBox i) farBox (nearLive i) farLive
  intro a
  refine Fin.cases ?_ (fun i=>?_) a
  · intro b
    exact Fin.cases (fun ne=>(ne rfl).elim) (fun j _=>cross j) b
  · intro b
    refine Fin.cases (fun _=>reverse (cross i)) (fun j distinct=>?_) b
    exact disjointly P (φ i) (φ j) x y gap (max zNear (T*zFar)) o positive fit
      (same i j (fun eq=>distinct (congrArg Fin.succ eq))) distanced
      ((nearBox i).trans (le_max_left ..)) ((nearBox j).trans (le_max_left ..)) (nearLive i) (nearLive j)

end YM.Integration.WilsonIndependentMovingRosterStableRoots
