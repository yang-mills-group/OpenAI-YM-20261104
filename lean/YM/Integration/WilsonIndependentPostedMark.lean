import YM.Integration.WilsonIndependentPostedProjection
import YM.Integration.WilsonIndependentConditionalRawSpout

/-! The funded full transformed source before and after the actual finite conditional. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedMark
open Filter Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open AnalyticNext.QuarticMatch.Sheets Work.F08 Next.Free PertExtension Tree FreeResolvent Metric Precision Exterior Wilson
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonIndependentConditionalUnshiftedQuiet (matrix)
open WilsonIndependentConditionalUnshiftedExit (ends)
open WilsonIndependentConditionalUnshiftedMark (word)
open WilsonIndependentConditionalRawSpout (finite)
open scoped Classical BigOperators Matrix
variable {G:Gauge}

theorem earned (P:Patch){k:ℕ}(U:Era G ℝ)(auth:Auth k U)(α:Cost)(e r:ℕ):
    Bends 0 (fun n=>word P (fun i=>mix α (U.1 i)) n e r)
      (slidesJ P 0 (mix α U.2) e r):=by
  apply WilsonIndependentConditionalUnshiftedMark.enrolled P (0:Site P.L)
  intro i s;rw [coat0]
  exact bend_mixX auth.wing α i s

theorem pure (P:Patch){k:ℕ}(U:Era G ℝ)(auth:Auth k U)(α:Cost)(n:Side)(i:ℕ):
    Pure (word P (fun v=>mix α (U.1 v)) n i):=by
  intro r π x
  exact fade_pure (mix_pure (auth.pale (n*P.L)) i) _ r π ((weaveH (ratioN P.L n) G).symm∘x)

theorem original (P:Patch)(K:KernelChoices)(H:FaceRow)(Q:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)
    (n:Side)(V F:Pal ℝ (Joint G (n*P.L) n))(k e r:ℕ)(q:Fin r→Woods G n):
    fade plug (fade (panSlice G (stepAt P K n) (xree P K n) (teller G P K Q n))
       (finite (fillSlots (Woods G n) (mer P K H n)) V F k e)) r q=
    scoop (fade (ends P K Q n) (finite (matrix P K H n) (fun i=>bend (weaveH (ratioN P.L n) G) (V i))
      (fun i=>bend (weaveH (ratioN P.L n) G) (F i)) k e) r) q:=by
  rw [WilsonIndependentPostedProjection.mean]
  congr 2
  rw [finite,bend_sum]
  apply Finset.sum_congr rfl;intro j _
  rw [sprint]
  congr 2
  funext b t
  exact bend_abr _ _ _ b t

end YM.Integration.WilsonIndependentPostedMark
