import YM.Integration.WilsonIndependentConditionalMerSlates
import YM.Integration.WilsonIndependentConditionalUnshiftedExit

/-! The reindexed joint heat, with its actual retained mean, is the original
finite Mer coefficient on each ordinary period and at each angular rank. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalMerPosted
open Filter Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalUnshiftedMark WilsonIndependentConditionalUnshiftedExit
open scoped BigOperators Classical
variable {G:Gauge}

theorem reindexed (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(H:FaceRow)(F:Crude G)
    (U:(n:Side)→Pal ℝ (Woods G n))(k:ℕ)(n:Side)(e:ℕ):
    bend (weaveH (ratioN P.L n) G) (WilsonIndependentConditionalMerSlates.slate (stepAt P K n) Ñ
      (mer P K H n) 0 (F (n*P.L)) (U (n*P.L)) k e)=finite P K Ñ H F U k n e:=by
  unfold WilsonIndependentConditionalMerSlates.slate finite
  rw [bend_sum,show 1+k+3*e=k+3*e+1 by omega]
  apply Finset.sum_congr rfl
  intro j _
  rw [sprint]
  simp_rw [bend_abr]
  rfl

theorem after {n:Side}{α β:Type}[Fintype α][Fintype β][DecidableEq α][DecidableEq β]
    (M:ropes (Site n) α β)(Z:Gen ℝ (Co n (α⊕β)))(r):
    scoop (fade (stair (upper 1 M) ladder) Z r)=scoop (fade (stair (upper 0 M) ladder) Z r):=by
  funext z
  unfold scoop fade
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (fun x:ℝ=>x • Z r y)
  apply Finset.prod_congr rfl
  intro i _
  cases hy:(y i).2 <;> simp [stair,upper,hy,Function.comp_apply,pierR]

theorem original (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(H:FaceRow)(Q)(F:Crude G)
    (U:(n:Side)→Pal ℝ (Woods G n))(k:ℕ)(n:Side)(e r:ℕ)
    (p:shellK 2 (F (n*P.L)))(rate:LocalRatio Ñ)(h:shellK k (U (n*P.L)))
    (hp:∀i,Pure (F (n*P.L) i))(hw:∀i,Pure (U (n*P.L) i))
    (b:P.Branches K G)(adj:(mer (G:=G) P K H n).transpose=mer P K H n):
    reed (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) k (U (n*P.L)) e r=
      scoop (fade (ends P K Q n) (finite P K Ñ H F U k n e) r):=by
  have moved:=WilsonIndependentConditionalMerSlates.original (stepAt P K n) Ñ (xree P K n) H (Q n)
      p rate h hp hw b adj e
  rw [moved,into_shade (ratioN P.L n),bend_fade (weaveH (ratioN P.L n) G) (weaveH (ratioN P.L n) G),
    ground_chart (ratioN P.L n) _ rfl,reindexed P K Ñ H F U k n e]
  exact after _ _ r

end YM.Integration.WilsonIndependentConditionalMerPosted
