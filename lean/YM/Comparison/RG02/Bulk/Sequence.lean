import YM.Comparison.RG02.Bulk.Fk
/-!
# Report binding to one actual Wilson sequence

Make one `Chain` (see `Chain.at_Oasis`), not independently `choose` at each order. This
 records which single Kin & charts to take, alpha/budget/loop convention. Same public path hC
 throughout. Keep equality of entire PathData etc. Cost receipts just the existing ones;
 require the actual steps also to KEEP the old certs. Extra precision/readouts (RG01+) not part of
 this structure, especially NO claims replacing alpha after repeated transports. Supplementary
 `W` (analytical packets: generator functions on gauge configurations and their Taylor
 coefficients) chosen after this; not per order token or per marker name unless comparing under
 Order restrictions. Use on real `Family.Makes` & Core integral clauses later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk
open Function Filter Precision RG RG.Supply Wilson Lattice Exterior Tree
open Marker
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge}

/-- Exact tie to `History C` of the prescribed actual output. Stores matching multiple-forest
 and order/input-independent witness for the prescribed *stationary portion*. `Kin.Planned`
 already contains enough quadratic data for our local matching of these low terms; doesn't assume
 high-order corrections. No adjacently-divided coupling coefficients here. Later kinetic costs can
 use that same `α`. Keep the price sheets with their pre/post stamps (only the Plan part needed
 here, not all simultaneous feasibility asserted from these values). -/
structure Chain (C : RG.History G) where
  preCosts : Sheet G
  lengths : Rolls preCosts
  post : PostCost lengths
  horizon : Horizon C.levels
  O : ChartRatio G
  receipt : LocalRatio O
  kin : Kin horizon O
  planned : kin.Planned post
  selected (N p m : ℕ) : m≤N → (C.rep N p m).path=kin.path N m
  clips (N p m : ℕ) : m≤N → (C.rep N p m).clip=(C.levels.params m).clip
variable {C : History G} (Y : Chain C)
namespace Chain
variable (N n p : ℕ)
local notation "S" => C.levels.clock.op n p
local notation "P" => C.rep N p n
local notation "R" => C.rep N p (n+1)

def step (h : n<N) : Kernel S (R).clip (R).path Y.O := by
  -- keep b definitionally, not a choice varying with mark addresses
  refine ⟨Y.kin.stationary N n p, Y.receipt, (C.levels.blocks n p).branches,?_,?_,?_⟩
  · intro F; rw [Y.selected N p _ h, Y.clips N p _ h]; exact (Y.planned.critical N n p h F).1
  · rw [Y.selected N p _ h,Y.clips N p _ h]; exact ⟨_,_,_,Y.planned.cap N _ h⟩
  intro F; rw [Y.selected N p _ h,Y.clips N p _ h]; exact ⟨_,Y.post.price _,Y.planned.gap N n p h F⟩

lemma keeps (h : n<N) (F : Forest (S).ratio) : ClassicalMatch F (R).clip (P).clip (R).path (P).path ((Y.step N n p h).b F) := by
   rw [show (Y.step N n p h).b=Y.kin.stationary N n p from rfl,Y.selected N p _ h,Y.clips N p _ h,Y.selected N p _ h.le,Y.clips N p _ h.le]; exact Y.planned.classicalPart N n p h F
include Y in
lemma peak (j : ℕ) (h : j≤4) : SameJet j (fun x=> mainTerm (C.rep N p N).clip (C.rep N p N).path (represent (x:fieldDir G (C.S.side N p) 1))) (fun x=> Wilson.energy (represent x)) := by
    rw [Y.clips N p N le_rfl, Y.selected N p N le_rfl]; exact Y.planned.peak N p j h
include Y in
lemma starts (b : ℕ) : ((C.rep N p N).path.loop b).coeff=0 := by rw [Y.selected N p N le_rfl]; exact Y.planned.initial N b
end Chain

end YM.Comparison.RG02.Bulk
