import YM.Integration.WilsonAllDateHarvestBoard
import YM.RG05Readout.Records.Dye

/-! The all-date marked representation for the actual Wilson push of each whole
cutoff column.  Each column includes its complete signed child sum and the
translated physical test at its own real address. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestPhysical
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]
    {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ)
variable (q:ManyStem C o n→Body)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "origins" => (A).supportX
local notation "tests" => headings o E q
variable (h:C.Makes) (L:OPE.Package C w r D) (stock:Storage C D)
variable (P:(j:W)→Sight C (s j) p) (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j))
variable {B:ℕ→ℕ→ℝ} {Q:ℝ} (roster:Census W)
local notation "Y" => C.path.rep N p
local notation "rows" => plants (m:=m) s P S x
local notation "vec" => Launch (m:=m) s S x

def columns (m N i:ℕ)(j:ManyStem C o i): Goods G (C.side N p):=
  clinic C p N (s (Λ i j)) (Launch (m:=m) s S x (Λ i j) N) i (origins i j) ((A).motion (Λ i j)) (tests i j)

include h L stock in
theorem original (basis:∀j:W,Spine D B h n p (s j) N (P j) (S j))
    (nm:n ≤ m) (mN:m ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (q j) 1)
    (sizeBound:∀j:W,size (x j) ≤ Q) (positive:0<Q) (warm:Warm C n (d+1) k) (degrees:∀j:W,s j ≤ d):
    ∀i,∀mi:m ≤ i,∀iN:i ≤ N,
      let X:=birth (Mine.ward o E roster i) (Y N) (columns o E s q S x m N i)
      Integrable X (prior G _) ∧
      MenuBoard (Y i) (imprint h A tests rows i iN)
        (fun U=>narrow (WilsonAllDateHarvestBoard.admitted o E roster nm mi) (gust C.path N p N X i iN U))
        (origins i) (fun _=>envelope C m (d+1) k Q i)
        (if i=N then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent) 1 := by
  let T:=swell (le_refl N) A s (fun j=>precinct C p N (s j) (vec j N)) tests
  let born:=fun j:ManyStem C o N=>stepUp ((A).motion (Λ N j)) (origins N j)
    (entrance C (s (Λ N j)) N p (vec (Λ N j) N) 0 (tests N j))
  let X:=birth (Mine.ward o E roster N) (Y N) born
  obtain ⟨F,replay,top⟩:=wind o E s (nm.trans mN) X
  have energy:Integrable X (prior G _) := seen_top A s tests h
  have tops:T N=born:=funext (staples A s tests (fun j=>vec j N))
  have eqn:F N=gust C.path N p N (birth (Mine.ward o E roster N) (Y N) (T N)) N le_rfl:=by
    rw [gust_base,tops]; exact top
  have integrable:Integrable (birth (Mine.ward o E roster N) (Y N) (T N)) (prior G _):=by
    rw [tops]; exact energy
  obtain ⟨start,prepared⟩:=headlines (N:=N) o E q
  have samples:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (tests n j) 1:=by rw [start]; exact cap
  have boards:=WilsonAllDateHarvestBoard.original o E s tests h L stock P S x roster basis nm mN
    occupied prepared samples sizeBound positive warm degrees top replay
  intro i mi iN X'
  have identified:=reimburses A s (le_refl N) T (le_refl n) replay
    (fun j nj jN=>pillar _ _ _ _ nj jN (prepared j nj jN)) eqn integrable (nm.trans mi) iN
  exact ⟨identified.1,identified.2 ▸ boards i mi iN⟩

end YM.Integration.WilsonAllDateHarvestPhysical
