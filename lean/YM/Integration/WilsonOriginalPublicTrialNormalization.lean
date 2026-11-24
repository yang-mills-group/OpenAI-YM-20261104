import YM.Integration.WilsonOriginalPublicTrialFigure
import YM.Integration.WilsonPositionProgramInversionRank
import YM.XSpace.VertexProducts

/-! Normalize the actual measured group function under one finite inversion vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonOriginalPublicTrialNormalization
open Finset Lattice Wilson RG Labels Source PhysicalNext.Repeat.Legato XSpace
open RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb Precision
open scoped Classical BigOperators ContDiff

private theorem combine {E ι J:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype ι][Fintype J]
    (b:Module.Basis ι ℝ E)(w:J→ℂ)(f:J→E→ℂ)(good:∀j,ContDiffAt ℝ ∞ (f j) 0):
    Taylor.expandTaylor b (fun x=>∑j,w j*f j x)=∑j,w j • Taylor.expandTaylor b (f j):=by
  apply PowerSeries.ext
  intro n
  apply Taylor.from_real b
  intro x
  have hn : (n:ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have smooth : ContDiffAt ℝ (n:ℕ∞ω) (fun y=>∑j,w j*f j y) 0 :=
    ContDiffAt.sum fun j _=>contDiffAt_const.mul ((good j).of_le hn)
  rw [Taylor.line_coeff b n x smooth,map_sum,map_sum]
  have rays (j:J):ContDiffAt ℝ (n:ℕ∞ω) (fun t:ℝ=>f j (t • x)) 0 := by
    let h:=ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
    exact ContDiffAt.comp (f:=h) (0:ℝ) (show ContDiffAt ℝ (n:ℕ∞ω) (f j) (h 0) by rw [map_zero]; exact (good j).of_le hn) h.contDiff.contDiffAt
  rw [iteratedDeriv_fun_sum (f:=fun j t=> w j * f j (t • x)) (fun j _=>contDiffAt_const.mul (rays j)),mul_sum]
  apply sum_congr rfl
  intro i _
  rw [PowerSeries.coeff_smul,map_smul,Taylor.line_coeff b n x ((good i).of_le hn)]
  change _ * iteratedDeriv n (fun t:ℝ=>w i • f i (t • x)) 0 = w i * (_ * _)
  rw [iteratedDeriv_fun_const_smul_field]
  ring

variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
local notation "F" j:max => R.family.labels.level (d j)
open WilsonOriginalPublicTrialFigure (measured weight)
open WilsonPositionProgramCopyTop (planted)

def series (g:ℝ)(v:∀i,(F i).Coeff)(z:I→ Cover)(p:Period)(T:p.Tree): PowerSeries ℂ:=
  Bare.normalized T G (Taylor.expandTaylor (T.basis G) (measured R d g v z ∘ T.links))

theorem filed (g:ℝ)(v:∀i,(F i).Coeff)(z:I→ Cover)(p:Period)(T:p.Tree):
    series R d g v z p T = ∑a,weight R d g v a • WilsonPositionProgramCopyTop.normalized R p d z a T:=by
  let f (a:∀i,(F i).Index):T.Field G→ℂ:=Complex.ofRealCLM ∘ (planted R p d z a ∘ T.links)
  have field:measured R d g v z ∘ T.links=fun x=>∑a,weight R d g v a * f a x:=by
    funext x
    exact WilsonOriginalPublicTrialFigure.opened R d g v z p.side (T.links x)
  have smooth a:ContDiffAt ℝ ∞ (f a) 0:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (FVA2.OrbGerm.tree T (WilsonPositionProgramCopyTop.allowed R p d z a))
  rw [series,field,combine _ _ _ smooth,map_sum]
  apply sum_congr rfl
  intro a _
  rw [map_smul];rfl

/-- The true normalized coefficient is the finite sum of independently evaluated
tree moments of the registered basis scouts, with each word's own depth. -/
theorem original (g:ℝ)(v:∀i,(F i).Coeff)(z:I→ Cover)(p:Period)(T:p.Tree)
    (D:ChartRatio G)(law:LocalRatio D)(q:ℕ):
    PowerSeries.coeff q (series R d g v z p T)=∑a,weight R d g v a *
      (if Kick.depthF univ d a ≤ q then
        ((YM.FVAAlt2.Fixed.treeMom D (planted R p d z a) (Kick.depthF univ d a)
          (q-Kick.depthF univ d a):ℝ):ℂ) else 0):=by
  rw [filed,map_sum]
  apply sum_congr rfl
  intro a _
  rw [PowerSeries.coeff_smul,smul_eq_mul]
  congr 1
  split
  · rename_i ok
    have h:=WilsonPositionProgramCopyTop.original R p d z a D law T (q-Kick.depthF univ d a)
    rwa [Nat.sub_add_cancel ok] at h
  · rename_i too
    exact WilsonPositionProgramInversionRank.original R p d z a T q (Nat.lt_of_not_ge too)

end YM.Integration.WilsonOriginalPublicTrialNormalization
end
