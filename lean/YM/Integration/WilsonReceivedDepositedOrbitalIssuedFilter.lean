import YM.Integration.WilsonReceivedDepositedOrbitalRatedFilter
import YM.Integration.WilsonOriginalCopiedContraction

/-! The original copied upper row, read after its kinetic correction on the normalized finite boards. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalIssuedFilter
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (R : Run G)
variable {V ι μ ν α : Type} [DecidableEq V] [Fintype V] {m n N : ℕ}
local notation "S" => R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "c" => R.family.side m n
local notation "f" => R.family.side (m+1) n
variable {J : Passport (R.family.side (m+1) n) V} {W : Census V}
variable (h : m < N)
variable (D : Layout G) (T : Finset Age) (p : ℕ) (M : ι → Row J W G α) (w : V → ℕ)
local notation "CC" => Covers R.family.path.levels.S m
local notation "CC'" => coverFilter R.family.path.levels.S m

open Comparison.RG02.Adjacent Comparison.RG02.Valence
variable (grid:Side)(inputs:∀b:CC grid,Bulk.Colors W G (R.family.side (m+1) b.val))
  (trees:∀b:CC grid,Forest (S m b.val).ratio)(tags:∀b:CC grid,(S m b.val).Choices)
def fieldRow {G:Gauge}(R:Run G){m N:ℕ}(h:m<N)(p:ℕ)(grid:Side){V:Type}[Fintype V][DecidableEq V]
    {W:Census V}
    (inputs:∀b:Covers R.family.path.levels.S m grid,Bulk.Colors W G (R.family.side (m+1) b.val))
    (trees:∀b:Covers R.family.path.levels.S m grid,Forest (R.family.path.levels.clock.op m b.val).ratio)
    (tags:∀b:Covers R.family.path.levels.S m grid,(R.family.path.levels.clock.op m b.val).Choices)
    (s:W.Mode)(b:Covers R.family.path.levels.S m grid)(e:ℕ)(Z:Stationary.Link G (R.family.side m b.val)):ℂ :=
  (Order.observe W p (Order.logMarked (Bulk.Fk ((RunFormalChain.fromRun R).step N m b.val h)
    (trees b) (tags b) (inputs b) (Stationary.arm G (R.family.side m b.val) 1 Z) p)) e).part s

def share (b:CC grid):ℂ:=Complex.ofReal ((Pages grid (R.family.side m b.val):ℝ)⁻¹)
open WilsonReceivedDepositedOrbitalCofinalLift (pulled)
theorem original {K₀:Passport (R.family.side m n) V}(Y:μ→Row K₀ W G α)
    (published:RepresentsCover R h D T p M w Y)(t:α)(grid:Side)
    (inputs:∀b:Covers R.family.path.levels.S m grid,Bulk.Colors W G (R.family.side (m+1) b.val))
    (trees:∀b:Covers R.family.path.levels.S m grid,Forest (R.family.path.levels.clock.op m b.val).ratio)
    (tags:∀b:Covers R.family.path.levels.S m grid,(R.family.path.levels.clock.op m b.val).Choices)
    (multiple:(R.family.side m n).val∣grid.val)
    (matched:∀ b:CC grid,copyColor (tiled R multiple b) M w (fun v=>(M v).paint t) D T=inputs b)
    (cost:UnitCost)(r d:ℕ)(kept:r≤p)(s:Multi.Hot W)(height:ℕ→ℕ)
    (fund:∀b:CC grid,Charge r (fun j=>(height j:ℤ)) (fieldRow R h p grid inputs trees tags s.val b))
    (Z:Stationary.Link G grid):
    Tendsto (fun b:CC grid=>share R grid b*born (fieldRow R h p grid inputs trees tags s.val b) cost 0 r d
      (convey (coverWin b.prop) Z)) (CC' grid)
      (𝓝 (born (fun e z=>(peek multiple Y w D T t e z).part s.val) cost 0 r d Z)):=by
  let H (j:ℕ):=max (height j) (Launch.index W w s.val+1+j)
  let received:=fieldRow R h p grid inputs trees tags s.val
  let restored (b:CC grid):Display (Stationary.Link G grid):=pulled (share R grid b) (convey (coverWin b.prop)) (received b)
  let selected:Display (Stationary.Link G grid):=fun e z=>(peek multiple Y w D T t e z).part s.val
  have reserved (b:CC grid):Charge r (fun j=>(H j:ℤ)) (received b):=fun j hj=>
    (fund b j hj).promote (Int.ofNat_le.mpr (le_max_left ..))
  have lower:Charge r (fun j=>(H j:ℤ)) selected:=fun j _=>
    (WilsonThermometerOriginalPupilDegree.copied multiple Y w D T t j s).promote (Int.ofNat_le.mpr (le_max_right ..))
  have nodes (j:ℕ)(bound:j≤r)(A:Stationary.Link G grid):
      Tendsto (fun b=>restored b j A) (CC' grid) (𝓝 (selected j A)):=by
    have sale:=WilsonOriginalCopiedContraction.named (R:=R) (h:=h) (p:=p) (M:=M) (Y:=Y)
      (published:=published) (t:=t) (grid:=grid) (multiple:=multiple) (inputs:=inputs) (matched:=matched)
      (F:=trees) (tag:=tags) (A:=A) (e:=j) (he:=bound.trans kept)
    exact ((Poly.part_cont s.val).tendsto _).comp sale
  apply WilsonReceivedDepositedOrbitalRatedFilter.original (CC' grid) (share R grid) (fun b=>convey (coverWin b.prop))
    received selected cost r d H reserved lower Z
  intro j hj a _
  exact nodes j hj ((a:ℝ) • Z)

end YM.Integration.WilsonReceivedDepositedOrbitalIssuedFilter
end
