import YM.Integration.WilsonOriginalPublicPivotReflected
import YM.Integration.WilsonOriginalPublicPivotPowers
import YM.Integration.WilsonOriginalPublicPivotSalary

/-! An exact compensated expansion on the original frozen numerical Figure.
Its normalized residuals are integrated jointly on the same finite top board
and then tested with the same root and center weights on each proper face. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
namespace YM.Integration.WilsonOriginalPublicPivotFaces
open Finset Filter PowerSeries Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicPivotReflected (sampled evaluated board)
open WilsonThermometerPositionTunedSlope (paid)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonThermometerPositionTunedCorrection (residual)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)(W:Initialize G){n:ℕ} (h:Fin n→ℕ)
    (v:(i:Fin n)→(R.family.labels.level (h i)).Coeff)
local notation "T" X:max => W.tree (X:Sample n).F.p
local notation "F" i:max => R.family.labels.level (h i)
local notation "z" X:max => fun i=>chartV X i

def raw (X:Sample n)(i:Fin n):Bare.Series (T X) G:=
  Bare.raw (T X) (W.surveys (h i)) (chartV X i) ((F i).coords.symm (v i)).val

def earlier (X:Sample n)(S:Finset (Fin n)):PowerSeries ℂ:=
  paid R (h ∘ Subtype.val:S→ℕ) (frozen R (h ∘ Subtype.val:S→ℕ) (fun i:S=>v i))
    (residual R W (h ∘ Subtype.val:S→ℕ) X.F.p (fun i:S=>X.layout i) (T X))

def part (proxy:(X:Sample n)→Fin n→Bare.Series (W.tree X.F.p) G)
    (X:Sample n) (S B:Finset (Fin n)):PowerSeries ℂ:=by
  let changed : Fin n → Bare.Series (W.tree X.F.p) G :=fun i=> (raw R W h v X i) - proxy X i
  exact Bare.normalized (W.tree X.F.p) G
    ((∏ i ∈ B, changed i) * (∏ i ∈ S \ B, proxy X i))

variable (P:(X:Sample n)→Fin n→Bare.Series (W.tree X.F.p) G)
theorem opened (X:Sample n)(S:Finset (Fin n)):
    board R W h v X S=earlier R W h v X S+∑B∈S.powerset,part R W h v P X S B:=by
  let I:S→ℕ:=h ∘ Subtype.val
  have file:=WilsonThermometerPositionTunedCorrection.earned R W I X.F.p (fun i:S=>X.layout i) (T X)
    (frozen R I (fun i:S=>v i))
  rw [WilsonOriginalPublicFigureWickFaces.folded R W h v X S] at file
  have words:(∏i∈S,raw R W h v X i)=∑B∈S.powerset,(∏i∈B,(raw R W h v X i-P X i))*(∏i∈S\B,P X i):=by
    rw [←Finset.prod_add];simp
  change board R W h v X S=earlier R W h v X S+∑B∈S.powerset,Bare.normalized (T X) G _
  rw [←map_sum,←words]
  exact (sub_eq_iff_eq_add.mp file)

private def evaluation (q:ℕ)(g:ℝ):PowerSeries ℂ→ₗ[ℂ]ℂ:=
  ∑k∈Finset.Iic q,(g:ℂ)^k • (coeff (R:=ℂ) k)
private theorem value (q:ℕ)(g:ℝ)(x:PowerSeries ℂ):evaluation q g x=evaluated q g x:=by
  simp only [evaluation,evaluated,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

variable {L:Type*}[Fintype L](X:L→Sample n)(μ:L→ℂ)(q:ℕ)(g:ℝ)
def tests (f:Sample n→PowerSeries ℂ):ℂ:=∑l,μ l*evaluated q g (f (X l))

theorem split (S:Finset (Fin n)):
    sampled R W h v X μ S q g - tests X μ q g (fun x=>part R W h v P x S ∅)=
      tests X μ q g (fun x=>earlier R W h v x S)+
      ∑B∈S.powerset.erase ∅,tests X μ q g (fun x=>part R W h v P x S B):=by
  have summand (l:L):μ l*evaluated q g (board R W h v (X l) S)=
      μ l*evaluated q g (earlier R W h v (X l) S)+
      (μ l*evaluated q g (part R W h v P (X l) S ∅)+
        ∑B∈S.powerset.erase ∅,μ l*evaluated q g (part R W h v P (X l) S B)):=by
    rw [opened R W h v P (X l) S,←value,map_add,map_sum,mul_add,mul_sum]
    simp only [value]
    exact congrArg (_ + ·) (add_sum_erase S.powerset (fun b=>μ l*evaluated q g (part R W h v P (X l) S b)) (mem_powerset.mpr (empty_subset S))).symm
  rw [sampled,tests,tests]
  simp only [summand,sum_add_distrib]
  rw [Finset.sum_comm (s:=univ) (t:=S.powerset.erase ∅)]
  change _ = _ + ∑B∈S.powerset.erase ∅,∑l,_
  abel

/-- The supplied estimate is on the summed root reading. Absolute values
are taken after the authentic signed ordinary test of each nonempty group. -/
theorem price (S:Finset (Fin n)){e a:ℝ}
    (ef:‖tests X μ q g (fun x=>earlier R W h v x S)‖≤e)
    (small:∀B∈S.powerset.erase ∅,‖tests X μ q g (fun x=>part R W h v P x S B)‖≤a):
    ‖sampled R W h v X μ S q g-tests X μ q g (fun x=>part R W h v P x S ∅)‖≤
      e+(S.powerset.erase ∅).card*a:=by
  rw [split]
  apply (norm_add_le ..).trans
  exact add_le_add ef ((norm_sum_le ..).trans (by simpa only [sum_const,nsmul_eq_mul] using sum_le_sum small))

end YM.Integration.WilsonOriginalPublicPivotFaces
end
