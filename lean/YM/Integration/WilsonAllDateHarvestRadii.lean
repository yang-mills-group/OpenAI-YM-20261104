import YM.Integration.WilsonAllDateHarvestRescaling

/-! Independently funded radii of the actual registered insertions on the original
cutoff-polynomial and the original singleton tapes at every high date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestRadii
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]
    {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (q:ManyStem C o n→Body)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "tests" => headings o E q
variable (h:C.Makes) (L:OPE.Package C w r D) (stock:Storage C D)
variable (P:(j:W)→Sight C (s j) p) (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j))
variable {B:ℕ→ℕ→ℝ} (roster:Census W) (Q:W→ℝ)
local notation "Y" => C.path.rep N p
local notation "rows" => plants (m:=m) s P S x
local notation "cols" => WilsonAllDateHarvestPhysical.columns o E s q S x m N

theorem positive {v:ℝ} (pv:0<v) (m d k i:ℕ):0<envelope C m d k v i:=
  mul_pos (rust_paid _).1 (grantw (totalpos pv i))

include h L stock in
theorem original (basis:∀j:W,Spine D B h n p (s j) N (P j) (S j))
    (nm:n ≤ m) (mN:m ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (q j) 1)
    (paid:∀j:W,size (x j) ≤ Q j) (qp:∀j:W,0<Q j) (warm:Warm C n (d+1) k) (degrees:∀j:W,s j ≤ d):
    ∀i,∀mi:m ≤ i,∀iN:i ≤ N,
      let X:=birth (Mine.ward o E roster i) (Y N) (cols i)
      Integrable X (prior G _) ∧
      MenuBoard (Y i) (imprint h A tests rows i iN)
        (fun U=>narrow (WilsonAllDateHarvestBoard.admitted o E roster nm mi) (gust C.path N p N X i iN U))
        ((A).supportX i) (fun j=>envelope C m (d+1) k (Q (Λ i j)) i)
        (if i=N then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent) 1:=by
  let z:=fun j:W=>(Q j)⁻¹
  let y:=fun j:W=>(z j:ℂ) • x j
  have unit(j:W):(Q j:ℂ)*(z j:ℂ)=1:=by
    dsimp only [z]; rw [Complex.ofReal_inv,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (qp j).ne')]
  have xx(j:W):size (y j)≤1:=by
    change size (((Q j)⁻¹:ℝ) • (x j))≤1
    rw [show ((Q j)⁻¹:ℝ) • x j=(((Q j)⁻¹:ℝ):ℂ) • x j from rfl,size_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (qp j))]
    calc (Q j)⁻¹*size (x j)=size (x j)/(Q j):=by ring
         _≤1:=(div_le_one (qp j)).mpr (paid j)
  intro i mi iN X
  let H:=Mine.masts o E nm (barren o E roster m) i
  let J:=Mine.ward o E roster i
  let inc:=WilsonAllDateHarvestBoard.admitted o E roster nm mi
  let l:=fun j:ManyStem C o i=>(Q (Λ i j):ℂ)
  let f:=WilsonAllDateHarvestPhysical.columns o E s q S y m N i
  let tape:=imprint h A tests (plants (m:=m) s P S y) i iN
  have actualCols:Many.combine id l f=cols i:=by
    rw [WilsonAllDateHarvestRescaling.own]; funext v
    rw [show f v=(z (Λ i v):ℂ) • cols i v from WilsonAllDateHarvestRescaling.source o E s q S x z iN v,
      smul_smul,show l v*(z (Λ i v):ℂ)=1 from unit _,one_smul]
  have actualRows:Many.combine id l tape=imprint h A tests rows i iN:=by
    rw [WilsonAllDateHarvestRescaling.own]; funext v
    rw [show tape v=(z (Λ i v):ℂ) • imprint h A tests rows i iN v from
      WilsonAllDateHarvestRescaling.row o E s q P S x z h iN v,
      smul_smul,show l v*(z (Λ i v):ℂ)=1 from unit _,one_smul]
  obtain ⟨integrable,board⟩:=WilsonAllDateHarvestPhysical.original o E s q h L stock P S y roster basis nm mN
    occupied cap xx zero_lt_one warm degrees i mi iN
  have lH:License H H id:=passable (Finset.Subset.refl _)
  have lJ:License J J id:=passable (Finset.Subset.refl _)
  let price:=fun v:ManyStem C o i=>envelope C m (d+1) k (Q (Λ i v)) i
  have exchange (v:ManyStem C o i):price (id v)*‖l v‖ ≤ envelope C m (d+1) k 1 i:=by
    change envelope C m (d+1) k (Q (Λ i v)) i*‖(Q (Λ i v):ℂ)‖≤_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (qp _)]
    exact (WilsonAllDateHarvestRescaling.width (qp _) mi).le
  have field:=board.blend l lH (h.wilson.represents N p i iN).good
    (q:=(A).supportX i) rfl exchange (fun _=>positive zero_lt_one ..) (fun v=>positive (qp _) ..)
  have bought:=Records.blended f l lJ iN integrable
  rw [actualCols] at bought
  refine ⟨bought.1,?_⟩
  have same:(fun U=>narrow inc (gust C.path N p N X i iN U))=
      fun U=>feed l lH (narrow inc (gust C.path N p N (birth J (Y N) f) i iN U)):=by
    unfold X
    rw [bought.2]
    funext U
    exact square l inc inc lH lJ _
  rw [same,←actualRows]
  exact field

end YM.Integration.WilsonAllDateHarvestRadii
