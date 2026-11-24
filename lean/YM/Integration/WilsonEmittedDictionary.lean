import YM.Integration.WilsonEmittedCompactTariff
import YM.Integration.WilsonEmittedTransitionJet
import YM.Integration.WilsonLimitConstruction.FundedDictionaryPatchPrices
import YM.Integration.NativePreselectedPostnumericPeriodRun
/-! The compact word fares are chosen on the actual original post-length menu before the Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedDictionary
open Filter Finset Lattice Wilson RG RG.Supply Precision
open Comparison.Density Comparison.Density.Transport
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.R2I.RG05Joint WilsonLimitConstruction FundedDictionaryPatchPrices
open scoped Classical BigOperators
universe v
variable {G:Gauge} (tube:LinkTube G)

def word (n s pieces shift:ℕ) := |WilsonEmittedTransitionJet.fee n shift
  (WilsonEmittedCompactTariff.fixed G n s pieces)|

def roster (k n:ℕ) := ∑ u ∈ range (k+1),∑ v ∈ range (k+1),∑ d ∈ range (k+1),word (G:=G) n u v d

def capacity (X:Patch) (k:ℕ) := k+X.J+1

def program : Cost := fun X _ B k =>
  let n:=max B.order k
  1 + roster (G:=G) (capacity X k) n + |groupPrice tube B.order| + (4:ℝ)^(B.power*B.order) +
    (13+n*(capacity X k)+2*B.power*B.order:ℕ) + ((X.L.val:ℝ)+1)^k + (2:ℝ)^(capacity X k)

private theorem term (f:ℕ→ℝ) {u k:ℕ} (P:∀z,0≤f z) (h:u≤k) :
    f u ≤ ∑z∈range (k+1),f z :=
  Finset.single_le_sum (f:=f) (fun z _=>P z) (mem_range.mpr (Nat.lt_succ_of_le h))

private theorem three (f:ℕ→ℕ→ℕ→ℝ) (P:∀ i j d,0≤f i j d) {i j d k:ℕ}
    (hi:i≤k) (hj:j≤k) (hd:d≤k) :
    f i j d ≤∑u∈range (k+1),∑v∈range (k+1),∑w∈range (k+1),f u v w := by
  let a u v:=∑w∈range (k+1),f u v w
  let b u:=∑v∈range (k+1),a u v
  have pa (u v:ℕ):0≤a u v:=sum_nonneg (fun w _=>P u v w)
  have pb (u:ℕ):0≤b u:=sum_nonneg (fun v _=>pa u v)
  exact (term (f i j) (P i j) hd).trans ((term (a i) (pa i) hj).trans (term b pb hi))

theorem school_word (B:Stage) (X:Patch) (K:KernelChoices) {s v d k:ℕ} (hs:s≤capacity X k) (hv:v≤capacity X k) (hd:d≤capacity X k) :
    word (G:=G) (max B.order k) s v d ≤ program tube X K B k := by
  let n:=max B.order k
  have e : word (G:=G) n s v d ≤ roster (G:=G) (capacity X k) n :=
    three (word (G:=G) n) (fun _ _ _=>abs_nonneg _) hs hv hd
  apply e.trans
  unfold program
  have full:0≤((X.L.val:ℝ)+1)^k:=by positivity
  have rent:0≤((13+n*(capacity X k)+2*B.power*B.order:ℕ):ℝ):=by positivity
  linarith [abs_nonneg (groupPrice tube B.order),show 0≤(4:ℝ)^(B.power*B.order) by positivity,show 0≤(2:ℝ)^(capacity X k) by positivity]

theorem covered_word (B:Stage) (X:Patch) (K:KernelChoices) {s v d k:ℕ} (hs:s≤k) (hv:v≤k) (hd:d≤k) :
    word (G:=G) (max B.order k) s v d ≤ program tube X K B k :=
  school_word tube B X K (hs.trans (by unfold capacity;omega))
    (hv.trans (by unfold capacity;omega)) (hd.trans (by unfold capacity;omega))

variable (Demand : Sheet G → MapPrices → Type v)
    (extra : ∀s q,Demand s q → ℕ → ℕ)
    (numeric : ∀s q,Demand s q → ℕ → ℕ → ℝ)
    (old : ∀s q,Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)

def costs : ∀s q,Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ :=
  fun s q ticket lengths k j => max |old s q ticket lengths k j| |post (program tube) s lengths k j|

theorem original (R:Run G)(simple:G.Simple)
    (paid:PostnumericPreselection Demand extra numeric (costs tube Demand old) R) :
    PostnumericPreselection Demand extra numeric old R ∧ Covered (program tube) R := by
  obtain ⟨s,q,ticket,n,base,floor,sheet,seed,raw,accrued,stage⟩:=paid
  let lengths := fun i=>(R.family.path.levels.clock.factor i).val
  let U:=old s q ticket lengths
  let V:=post (program tube) s lengths
  have left:NativeDiagonalClockRequest.PaidRequests U R.family.path.levels :=
    FundedDictionaryRenderPrices.paid_part (fun k i=>
      (le_max_left |U k i| |V k i|).trans (le_abs_self _)) accrued
  have right:NativeDiagonalClockRequest.PaidRequests V R.family.path.levels :=
    FundedDictionaryRenderPrices.paid_part (fun k i=>
      (le_max_right |U k i| |V k i|).trans (le_abs_self _)) accrued
  have edge:NativePostLengthPayment.StagePaid (U 0) R.family.path.levels:=fun m=>
    (le_abs_self _).trans ((le_max_left _ _).trans (stage m))
  exact ⟨⟨s,q,ticket,n,base,floor,sheet,seed,raw,left,edge⟩,
    FundedDictionaryPatchPrices.covered (program tube) R simple s n sheet right⟩

end YM.Integration.WilsonEmittedDictionary
