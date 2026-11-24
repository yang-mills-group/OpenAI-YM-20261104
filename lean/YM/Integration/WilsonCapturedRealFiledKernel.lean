import YM.Integration.WilsonCapturedPinnedGroupClock
import YM.RegulatorIR.Primitives.Hear

/-! A real finite-order group reading gives its original symmetric tensor
on all ordered fine links, including repeated sites and grade zero. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedRealFiledKernel
open Function Finset Lattice RG Wilson Marker QuadraticLocal Stationary
open Comparison.RG02.Adjacent
open Comparison.RG02 Multi RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline
open RegulatorIR.Budget RegulatorIR.Budget.Tuple RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Prim
open RegulatorIR.Binding RegulatorIR.FVAAlt2.Booth WilsonOriginalLinkedAngularPage
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}
local notation "I" => Site n×Loc G 1
local notation "E" => Link G n

def entries (F:ℕ→E→ℝ):Orders I:=fun e r x=>(r.factorial:ℝ)⁻¹ •
  iteratedFDeriv ℝ r (F e) 0 (fun i=>ray G (x i))

private theorem split (x:E): x=∑v:I,x v •ray G v:=by
  ext v
  simp [WilsonOriginalLinkedAngularPage.ray,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,mul_ite]

private theorem play (F:ℕ→E→ℝ)(e r:ℕ)(x:E):
    Assembly.jet (F e) r x=strum (entries F e r) x:=by
  let T:=(iteratedFDeriv ℝ r (F e) 0).toMultilinearMap
  change (r.factorial:ℝ)⁻¹ • T (fun _=>x) = _
  have even:(fun _ : Fin r=>x)=(fun _ : Fin r=>∑v:I,x v • ray G v):=funext fun _=>split x
  rw [even,MultilinearMap.map_sum_finset,Fintype.piFinset_univ,Finset.smul_sum]
  unfold strum
  rw [tsum_fintype]
  apply sum_congr rfl;intro a _
  rw [T.map_smul_univ]
  simp only [entries,noodle,smul_eq_mul]
  dsimp [T];ring

theorem symmetric (F:ℕ→E→ℝ)(smooth:∀e,ContDiffAt ℝ ω (F e) 0):
    gradedSymmetric (entries F):=by
  intro e r σ x
  apply congrArg ((r.factorial:ℝ)⁻¹ • ·)
  exact (smooth e).iteratedFDeriv_comp_perm (fun i=>WilsonOriginalLinkedAngularPage.ray G (x i)) σ

theorem degree (F:ℕ→E→ℝ){e m:ℕ}(lev:Valence.Level (e+m:ℕ) (F e)):
    Within (e+m) (entries F e):=by
  intro j h
  by_contra tooHigh
  apply h
  funext x
  unfold entries
  rw [lev.high j (by exact_mod_cast lt_of_not_ge tooHigh) 0]
  simp

theorem diagonal (F:ℕ→E→ℝ){e m:ℕ}(lev:Valence.Level (e+m:ℕ) (F e))(x:E):
    F e x=PowerSeries.coeff e (flavor m x (entries F)):=by
  rw [flavor_lo,←speaking,lev.posted x]
  unfold drums
  apply sum_congr rfl;intro a _;exact play F e a x

theorem original {L:Type}[DecidableEq L] {J:Census L} (C:UnitCost)(Z:Bulk.Colors J G n)(u:L)(H m:ℕ)
    (F:ℕ→E→ℝ)(levels:∀e,Valence.Level (e+m:ℕ) (F e))
    (issued:∀e≤H,∀a:E,See.noseC J u C Z e (Stationary.arm G n 1 a)=(F e a:ℂ)):
    Arm.Single C Z (entries F) u H m:=by
  refine ⟨symmetric F (fun e=>(levels e).smooth.contDiffAt),fun e=>degree F (levels e),?_⟩
  intro e he x
  have paid:=issued e he ((Stationary.arm G n 1).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply,diagonal F (levels e)] at paid
  exact paid

end YM.Integration.WilsonCapturedRealFiledKernel
