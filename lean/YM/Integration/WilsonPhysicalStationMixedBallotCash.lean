import YM.Integration.WilsonPhysicalStationPureBorn
import YM.Integration.WilsonPhysicalStationMixedBilledPort
/-! The finite signed coefficients remain outside the norm until the two complete readings have been subtracted. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedBallotCash
open Filter Lattice Wilson RG Source Cells Extraction Table Climb Trace.Pilot Next.UVStress PhysicalNext.Repeat.Legato
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price

open WilsonPhysicalStationFullVote (Head)
open WilsonPhysicalStationPureReceipt (coefficients ballot)
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonOriginalBlissMixedGram (grades)
open scoped BigOperators Classical
variable {I K:Type*}[Fintype I][Fintype K]

theorem transpose (μ:I→ℂ)(c:K→ℂ)(upper:I→ℂ)(lower:K→I→ℂ):
    ∑a,μ a*(upper a-∑j,c j*lower j a)=
      (∑a,μ a*upper a)-∑j,c j*(∑a,μ a*lower j a):=by
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted (μ u v:I→ℂ)(χ:ℂ)(t P W:ℝ)(tp:0 ≤ t)
    (cash:∀i,μ i≠0→‖u i-χ*v i‖*t ≤ W*P):
    ‖(∑i,μ i*u i)-χ*(∑i,μ i*v i)‖*t ≤ (∑i,‖μ i‖)*W*P:=by
  have eq:(∑i,μ i*u i)-χ*(∑i,μ i*v i)=∑i,μ i*(u i-χ*v i):=by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [eq]
  calc
    _ ≤ (∑i,‖μ i‖*‖u i-χ*v i‖)*t :=by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right
        (norm_sum_le (s:=Finset.univ) (fun i=>μ i*(u i-χ*v i))) tp
    _ = ∑i,‖μ i‖*(‖u i-χ*v i‖*t) :=by simp only [Finset.sum_mul,mul_assoc]
    _ ≤ ∑i,‖μ i‖*(W*P) :=by
      apply Finset.sum_le_sum
      intro i _
      by_cases live:μ i=0
      · simp [live]
      · exact mul_le_mul_of_nonneg_left (cash i live) (norm_nonneg _)
    _ = _ :=by rw [←Finset.sum_mul];ring

variable {G:Gauge}(R:Run G){S:Table R.family.book}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){h k r:ℕ}(q:ℕ)
local notation "C₀"=>standard R.family

def pair {L:Register G}(S:Table L)(h r:ℕ)(x:Points 2)(u:S.Field h)(v:S.Field r):ℂ:=
  S.classMoment S (grades h r) x (Fin.cons (α:=fun i=>S.Field (grades h r i)) u (fun _=>v))

theorem free (u:(C₀).Field h)(z:(C₀).Field r)(x:Points 2):
    (∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i*base R h z x i.val)=
      pair (C₀) h r x (ballot R J₀ J V (k:=k) q u) z:=by
  let M:=(C₀).classMoment (C₀) (grades h r) x
  let p:(i:Fin 2)→(C₀).Field (grades h r i):=Fin.cons (α:=fun i=>(C₀).Field (grades h r i)) 0 (fun _=>z)
  let L: (C₀).Field h→ₗ[ℂ]ℂ:=M.toLinearMap p 0
  have acts (b:(C₀).Field h):L b=pair (C₀) h r x b z:=by
    change M (Function.update p 0 b)=M (Fin.cons (α:=fun i=>(C₀).Field (grades h r i)) b (fun _=>z))
    exact congrArg _ (funext fun i=>by fin_cases i <;>simp [Function.update,p])
  rw [←acts,←WilsonPhysicalStationPureBorn.assembled R J₀ J V (k:=k) q u,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp only [acts]
  rfl

end YM.Integration.WilsonPhysicalStationMixedBallotCash
end
