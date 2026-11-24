import YM.Integration.WilsonPhysicalHistoryRetainedSpringBareSite
import YM.Next.STATIONARY.Shape.ClassicalMatch

/-! Number the original ordered pairs in the entering kinetic row once. Both
members retain their true lifted paths and their original scalar coefficients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice RG Wilson Precision Stationary
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side}

private def pairIndices : ℕ ≃ PairsIndex:=Classical.choice nonempty_equiv_of_countable

def gramEntries (K : PathData G) (i : ℕ) : Atom G 2:=gramPath K (pairIndices i)

theorem gram_finance (K : PathData G) {B : Clip} {σ D Λ : ℝ} (paid : K.Bounds B σ D Λ) :
    SumBudget (fun i=>(gramEntries K i).budget σ) (gramCost G D) := by
  have h:=gram_budget K (σ:=σ) (A:=D) paid.rows
  refine ⟨fun i=>h.1 (pairIndices i),pairIndices.summable_iff.mpr h.2.1,?_⟩
  exact (pairIndices.tsum_eq (fun i=>(gramPath K i).budget σ)).le.trans h.2.2

def facePriceAt (x : Site n) (U : Config G n) : ℝ :=
  Patch.average fun s : Signed=>∑ a : PlaqAxes,G.price (faceValue (pull s 0 U) (x,a))

theorem gram_at (K : PathData G) {B : Clip} {σ D Λ : ℝ} (paid : K.Bounds B σ D Λ)
    (x : Site n) (U : Config G n) :
    secondAt B K x U=B.direct*facePriceAt x U+sitePacket (gramEntries K) x U := by
  have same (s : Signed) : quadraticAt B K x (pull s 0 U)=
      B.direct*(∑ a : PlaqAxes,G.price (faceValue (pull s 0 U) (x,a)))+
      ∑' i,(gramEntries K i).unmasked (pull s 0 U) x:=by
    rw [quadraticAt,sum_add_distrib,←mul_sum]
    congr 1
    change _=∑' i,aTerm (gramPath K (pairIndices i)) (expandAt x (pull s 0 U))
    rw [pairIndices.tsum_eq (fun i=>aTerm (gramPath K i) (expandAt x (pull s 0 U))),gram_sums K paid]
  simp only [secondAt,facePriceAt,sitePacket,Patch.average,same,sum_add_distrib,←mul_sum]
  ring

end YM.Integration.OriginalMarkedRunAction
