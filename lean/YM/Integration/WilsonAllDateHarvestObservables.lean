import YM.Integration.WilsonAllDateHarvestPhysical
import YM.Integration.ActualTrajectoryTransport

/-! Normalized conditional products, including singletons, on the same original
Wilson field and the same true source columns at every ultraviolet date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestObservables
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N i d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]
    {B B':Census W} {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
local notation "Y" => C.path.rep N p

theorem normalized (iN:i ≤ N) (f:W→Goods G (C.side N p)) (included:B'.choices ⊆ B.choices)
    (paid:Integrable (birth B (Y N) f) (prior G _)) (q:B'.Mode) (U:Config G (C.side i p)):
    (((Y i).eval U:ℂ)⁻¹)*(narrow included (gust C.path N p N (birth B (Y N) f) i iN U)).part q=
      actualTransport C (N:=N) (fun V=>∏j∈q.val,f j V) iN U:=by
  let q':=route included q
  have actual:(fun V=>(birth B (Y N) f V).part q')=fun V=>((Y N).eval V:ℂ)*(∏j∈q.val,f j V):=by
    funext V; unfold birth Mach
    rw [Poly.part_smul,pass_fire]
    rfl
  rw [narrow_right]
  have eqn:=congr_fun (pushpart iN (birth B (Y N) f) q' paid) U
  rw [show (gust C.path N p N (birth B (Y N) f) i iN U).part (route included q)=_ from eqn,actual]
  simp only [actualTransport,Complex.real_smul,Complex.ofReal_inv]

variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (q:ManyStem C o n→Body)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "tests" => headings o E q
variable (h:C.Makes) (L:OPE.Package C w r D) (stock:Storage C D)
variable (P:(j:W)→Sight C (s j) p) (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j))
variable {capbook:ℕ→ℕ→ℝ} {Q:ℝ} (roster:Census W)
local notation "rows" => plants (m:=m) s P S x
local notation "f" => WilsonAllDateHarvestPhysical.columns o E s q S x m N

include h L stock in
theorem original (basis:∀j:W,Spine D capbook h n p (s j) N (P j) (S j))
    (nm:n ≤ m) (mN:m ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (q j) 1)
    (sizeBound:∀j:W,size (x j) ≤ Q) (positive:0<Q) (warm:Warm C n (d+1) k) (degrees:∀j:W,s j ≤ d):
    ∀i,∀mi:m ≤ i,∀iN:i ≤ N,
      let inc:=WilsonAllDateHarvestBoard.admitted o E roster nm mi
      let X:=birth (Mine.ward o E roster i) (Y N) (f i)
      let field:=fun U=>narrow inc (gust C.path N p N X i iN U)
      (∀U,∀v:(Mine.masts o E nm (barren o E roster m) i).Mode,
        (((Y i).eval U:ℂ)⁻¹)*(field U).part v=
          actualTransport C (N:=N) (fun V=>∏j∈v.val,f i j V) iN U) ∧
      (∀U,∀v:ManyStem C o i,actualTransport C (N:=N) (f i v) iN U=
        (((Y i).eval U:ℂ)⁻¹)*(imprint h A tests rows i iN v).1 U) := by
  intro i mi iN inc X field
  obtain ⟨integrable,board⟩:=WilsonAllDateHarvestPhysical.original o E s q h L stock P S x roster basis
    nm mN occupied cap sizeBound positive warm degrees i mi iN
  have coefficients(U)(v):=normalized iN (f i) inc integrable v U
  refine ⟨coefficients,?_⟩
  intro U v
  let T:=Mine.masts o E nm (barren o E roster m) i
  have eqn:=coefficients U (T.fire v)
  have singleton:(fun V=>∏j∈(T.fire v).val, f i j V)=f i v:=by
    funext V; change (∏j∈({v}:Finset _),_)=_; rw [Finset.prod_singleton]
  rw [singleton] at eqn
  exact eqn.symm.trans (congr_arg (fun z:ℂ=>(((Y i).eval U:ℂ)⁻¹)*z)
    ((board.check (h.wilson.represents N p i iN).good.labels U).2 v))

end YM.Integration.WilsonAllDateHarvestObservables
