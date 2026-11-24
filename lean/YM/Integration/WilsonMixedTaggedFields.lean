import YM.Integration.WilsonMixedTaggedSeparatedBoard
import YM.RG05Readout.Records.Dye

/-! The full physical field being reopened on the reporting day is the dated
ordinary Wilson push. Its dormant modes vanish throughout a single measured
history, including before division by the vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedFields

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Next.Rank.Station
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped BigOperators Classical

variable {G:Gauge} {C:Family G} {n m p N d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]
variable (o:W → Site (C.side n p)) (E:W → Motion) (s:W → ℕ) (q:ManyStem C o n → Body)
variable (S:(j:W) → Emblems C (s j)) (x:(j:W) → Palette C (s j)) (roster:Census W)
variable (h:C.Makes)
set_option quotPrecheck false
local notation "A" => Mine.tree o E
local notation "Y" => C.path.rep N p
local notation "I" => headings o E q
local notation "H" => Mine.ward o E roster
local notation "v" => Launch (m:=m) s S x
def columns (m N i:ℕ)(j:ManyStem C o i): Goods G (C.side N p):=
  clinic C p N (s ((A).labelY i j)) (Launch (m:=m) s S x ((A).labelY i j) N) i
    ((A).supportX i j) ((A).motion ((A).labelY i j)) (I i j)
local notation "cols" => columns o E s q S x m N
local notation "dark" => shadow A s I
local notation "field" => fun (i:ℕ) (iN:i ≤ N)=>
  gust C.path N p N (birth (H i) (Y N) (cols i)) i iN

variable {D:Address.Rail C} {worth:Worth} {rates:ℕ → ℕ} {B:ℕ → ℕ → ℝ} {Q:ℝ}
variable (book:OPE.Package C worth rates D) (stock:Storage C D) (P:(j:W) → Sight C (s j) p)
local notation "rows" => imprint h A I (plants (m:=m) s P S x)
include book stock in
theorem program (nm:n ≤ m) (mN:m ≤ N)
    (spine:∀j:W,Spine D B h n p (s j) N (P j) (S j))
    (occ:Occupancy o (C.path.levels.clock.J n))
    (caps:∀j:ManyStem C o n,Cap (s ((A).labelY n j)+2) (q j) 1)
    (charge:∀j:W,size (x j) ≤ Q) (pos:0 < Q) (warm:Warm C n (d+1) k) (degrees:∀j:W,s j ≤ d) :
    ∃ F:∀i,Config G (C.side i p) → Poly (H i), Replay A s (le_refl n) N F N ∧ 
      (∀i,n ≤ i → ∀iN:i ≤ N,F i=field i iN ∧ 
        ∀U (a:(H i).Mode),¬Disjoint (dark i) (a.val:Set _) → (F i U).part a=0) ∧ 
      MenuBoard (Y m) (rows m mN)
        (fun U=>narrow (WilsonMixedTaggedSeparatedBoard.admitted o E roster nm (le_refl m)) (F m U))
        ((A).supportX m) (fun _=>envelope C m (d+1) k Q m)
        (if m=N then (C.path.levels.budget m).supportExponent-4 else (C.path.levels.budget m).supportExponent) 1 := by
  have nN:=nm.trans mN
  let T:=swell (le_refl N) A s (fun j=>precinct C p N (s j) (v j N)) I
  let born:=fun j:ManyStem C o N=>stepUp ((A).motion ((A).labelY N j)) ((A).supportX N j)
    (entrance C (s ((A).labelY N j)) N p (v ((A).labelY N j) N) 0 (I N j))
  let X:=birth (H N) (Y N) born
  obtain ⟨F,replay,top⟩:=wind o E s nN X
  have energy:Integrable X (prior G _):=seen_top A s I h
  have tops:T N=born:=funext (staples A s I (fun j=>v j N))
  have eqn:F N=gust C.path N p N (birth (H N) (Y N) (T N)) N le_rfl:=by
    rw [gust_base,tops]
    exact top
  have integrable:Integrable (birth (H N) (Y N) (T N)) (prior G _):=by rw [tops];exact energy
  obtain ⟨base,prepared⟩:=headlines (N:=N) o E q
  have start:∀j:ManyStem C o n,Cap (s ((A).labelY n j)+2) (I n j) 1 := by rw [base]; exact caps
  have paid:=WilsonMixedTaggedSeparatedBoard.original o E s I h book stock P S x roster spine nm mN
    occ prepared start charge pos warm degrees top replay m (le_refl m) mN
  refine ⟨F,replay,?_,paid⟩
  intro i ni iN
  have identified:=reimburses A s (le_refl N) T (le_refl n) replay
    (fun j nj jN=>pillar _ _ _ _ nj jN (prepared j nj jN)) eqn integrable ni iN
  refine ⟨identified.2,?_⟩
  exact fun U a crossed=>replay.black A s (dark) (le_refl n) nN (top.symm ▸ energy) le_rfl
    (fun j nj jN z=>spilled A s I (le_refl n) prepared z nj jN)
    (fun V j miss=>by rw [top];exact birth_dark (dark N) (muted_atom A s I) _ _ miss)
    ni iN U a crossed

end YM.Integration.WilsonMixedTaggedFields
