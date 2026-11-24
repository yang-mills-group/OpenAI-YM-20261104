import YM.Integration.WilsonIndependentPostedBoard
import YM.Integration.WilsonIndependentConditionalRawVacuum

/-! The normalized finite plate on its retained coordinates, including the scalar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedProjection
open Function Matrix Lattice Laurent RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open AnalyticNext.QuarticMatch.Sheets Bloch Work.F08 Next.Free PertExtension Tree FreeResolvent Metric Precision Exterior Wilson
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open RegulatorIR.Oracle RegulatorIR.Calibration
open WilsonIndependentConditionalUnshiftedQuiet (matrix)
open WilsonIndependentConditionalUnshiftedExit (ends)
open WilsonIndependentConditionalRawVacuum (finite)
open scoped Classical BigOperators Matrix

variable {G:Gauge}

private theorem held {f c:Side}(S:StepData c f)(F:Forest S.ratio)(M:Matrix (Woods G f) (Woods G c) ℝ)
    (i:Joint G f c)(v:Woods G c):
    panSlice G S F M i (.inr v)=groundM G M i (.inr v):=by
  classical
  simp [panSlice,overM,bridgeM,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂,Matrix.one_apply]

theorem mean (P:Patch)(K:KernelChoices)(Q:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)
    (n:Side)(J:Gen ℝ (Joint G (n*P.L) n))(r:ℕ)(q:Fin r→Woods G n):
    fade plug (fade (panSlice G (stepAt P K n) (xree P K n) (teller G P K Q n)) J) r q=
      scoop (fade (ends P K Q n) (bend (weaveH (ratioN P.L n) G) J) r) q:=by
  let g:=ratioN P.L n
  let E:=weaveH g G
  let M:=teller G P K Q n
  rw [fade_plug]
  change fade _ J r (Sum.inr ∘ q)=_
  have ha:fade (panSlice G (stepAt P K n) (xree P K n) M) J r (Sum.inr∘q)=
      fade (groundM G M) J r (Sum.inr∘q):=by
    unfold fade;apply Finset.sum_congr rfl;intro y _
    congr 1;apply Finset.prod_congr rfl;intro j _;exact held _ _ _ _ _
  rw [ha]
  have hb:=congrFun (congrFun (bend_fade E E (groundM G M) J) r) (pierR∘q)
  have hc:bend E (fade (groundM G M) J) r (pierR∘q)=fade (groundM G M) J r (Sum.inr∘q):=by
    change fade _ _ _ (E.symm ∘ pierR ∘ q)=_
    congr 1
  rw [←hc,hb,ground_chart g M rfl]
  unfold scoop ends fade
  apply Finset.sum_congr rfl;intro y _
  congr 1

theorem original (P:Patch)(K:KernelChoices)(H:FaceRow)(Q:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)
    (n:Side)(V:Pal ℝ (Joint G (n*P.L) n))(e r:ℕ)(q:Fin r→Woods G n):
    fade plug (fade (panSlice G (stepAt P K n) (xree P K n) (teller G P K Q n))
       (finite (fillSlots (Woods G n) (mer P K H n)) V e)) r q=
    scoop (fade (ends P K Q n) (finite (matrix P K H n) (fun i=>bend (weaveH (ratioN P.L n) G) (V i)) e) r) q:=by
  rw [mean]
  congr 2
  rw [finite,bend_sum]
  exact Finset.sum_congr rfl (fun j _=>bend_abr _ _ _ j e)

end YM.Integration.WilsonIndependentPostedProjection
