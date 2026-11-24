import YM.Integration.WilsonCapturedOccupiedClockTaylor
import YM.Integration.WilsonPositionProgramDatedClockBill

/-! Ordered angular derivatives of the filed polynomial in its own coupling clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedClockRankProjection
open Function Finset Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Assembly
open Comparison.RG02.Moving.Path YM.Analysis Valence
open scoped Classical ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem excess (f:E→ℂ) (smooth:ContDiffAt ℝ ω f 0) {j r:ℕ}(hr:j<r):
    iteratedFDeriv ℝ r (Work.G05.blockTaylor j f) 0=0:=by
  have ready (a:ℕ):ContDiff ℝ r (Assembly.jet f a):=(Adjacent.levelJet smooth a).smooth.of_le le_top
  change iteratedFDeriv ℝ r (∑a∈range (j+1),Assembly.jet f a) _=0
  rw [show (∑a∈range (j+1),Assembly.jet f a)=(fun x=>∑a∈range (j+1),Assembly.jet f a x) from funext fun x=>sum_apply ..,
    iteratedFDeriv_fun_sum_apply (fun a _=>(ready a).contDiffAt)]
  apply sum_eq_zero
  intro a ha
  exact (Adjacent.levelJet smooth a).high r (by have le:=mem_range_succ_iff.mp ha;omega) _

theorem projection (f:E→ℂ) (smooth:ContDiffAt ℝ ω f 0) (j r:ℕ)(hr:0<r) :
    iteratedFDeriv ℝ r (Assembly.jet f j) 0=if j=r then iteratedFDeriv ℝ r f 0 else 0:=by
  rcases lt_or_ge j r with high|low
  · rw [if_neg high.ne]
    exact (Adjacent.levelJet smooth j).high r (by omega) _
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:j≠0)
  let old:=Work.G05.blockTaylor k f
  have add:Work.G05.blockTaylor (k+1) f=old+Assembly.jet f (k+1):=by
    unfold Work.G05.blockTaylor old
    rw [sum_range_succ]
    rfl
  have preserved:=Work.G05.blockTaylor_jets (smooth.of_le le_top) r low
  rw [add,iteratedFDeriv_add_apply (Work.G05.blockTaylor_contDiff k f r).contDiffAt
    ((Adjacent.levelJet smooth (k+1)).smooth.of_le le_top).contDiffAt] at preserved
  by_cases equal:k+1=r
  · rw [if_pos equal]
    rw [show iteratedFDeriv ℝ r old 0=0 from excess f smooth (by omega),zero_add] at preserved
    exact preserved
  · rw [if_neg equal]
    have was:iteratedFDeriv ℝ r old 0=iteratedFDeriv ℝ r f 0:=Work.G05.blockTaylor_jets (smooth.of_le le_top) r (by omega)
    exact (add_eq_left.mp (was ▸ preserved))

def charge (C:UnitCost) (d:ℤ) (q r:ℕ) (fare:ℕ→ℝ):ℝ:=
  ∑i∈range (q+1),‖motion (money C d i r) q‖*fare i

private theorem finite {I:Type*} (S:Finset I) (f:I→E→ℂ)
    (sm:∀i∈S,ContDiff ℝ ω (f i)) (r:ℕ)(x:Fin r→E):
    iteratedFDeriv ℝ r (fun y=>∑i∈S,f i y) 0 x=∑i∈S,iteratedFDeriv ℝ r (f i) 0 x:=by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi=>((sm i hi).of_le le_top).contDiffAt),_root_.sum_apply]

theorem original (C:UnitCost)(d:ℤ)(q r:ℕ)(hr:0<r)(U:Display E)(levels:Charge q (fun i=>(i:ℤ)) U)
    (x:Fin r→E):
    iteratedFDeriv ℝ r (born U C d q q) 0 x=
      ∑i∈range (q+1),motion (money C d i r) q * iteratedFDeriv ℝ r (U i) 0 x:=by
  have rep:born U C d q q=(fun y=>∑i∈range (q+1),∑j∈range (i+1),
    motion (money C d i j) q*Assembly.jet (U i) j y):=by
    funext y
    simpa only [Int.toNat_natCast] using message C d q levels q y
  let row (i j:ℕ):E→ℂ:=fun y=>motion (money C d i j) q*Assembly.jet (U i) j y
  have smooth (i:ℕ)(hi:i≤q)(j:ℕ):ContDiff ℝ ω (row i j):=
    contDiff_const.mul (Adjacent.levelJet ((levels i hi).smooth.contDiffAt) j).smooth
  rw [rep,finite (range (q+1)) (fun i y=>∑j∈range (i+1),row i j y)
    (fun i hi=>ContDiff.sum (fun j _=>smooth i (mem_range_succ_iff.mp hi) j))]
  apply sum_congr rfl
  intro i hi
  have ok:ContDiffAt ℝ ω (U i) 0:=(levels i (mem_range_succ_iff.mp hi)).smooth.contDiffAt
  rw [finite (range (i+1)) (row i) (fun j _=>smooth i (mem_range_succ_iff.mp hi) j)]
  have each (j:ℕ):iteratedFDeriv ℝ r (row i j) 0 x=
      if j=r then motion (money C d i j) q*iteratedFDeriv ℝ r (U i) 0 x else 0:=by
    change iteratedFDeriv ℝ r (motion (money C d i j) q • Assembly.jet (U i) j) 0 x=_
    rw [iteratedFDeriv_const_smul_apply ((Adjacent.levelJet ok j).smooth.of_le le_top).contDiffAt,
      smul_apply,projection (U i) ok j r hr]
    split_ifs <;> simp [smul_eq_mul]
  simp_rw [each]
  by_cases present:r ≤ i
  · simp [mem_range_succ_iff.mpr present]
  · have dead:= (levels i (mem_range_succ_iff.mp hi)).high r (by change (i:ℤ)<r;omega) (0:E)
    simp [dead]

end YM.Integration.WilsonCapturedClockRankProjection
