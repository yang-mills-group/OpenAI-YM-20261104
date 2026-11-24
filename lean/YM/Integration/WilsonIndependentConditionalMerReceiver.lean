import YM.Integration.WilsonIndependentConditionalMerPosted

/-! The complete source on the original cover is the unshifted enrolled
heat followed by the actual held-field predictor and the common reset. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalMerReceiver
open Filter Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalUnshiftedMark WilsonIndependentConditionalUnshiftedExit
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem symmetric {c f:Side}(S:StepData c f)(T:Forest S.ratio)(H:FaceRow)(z:(H.acts f).transpose=H.acts f):
    (covariance G S T H).transpose=covariance G S T H:=by
  have inv:(treeInverse G S T H 0).transpose=treeInverse G S T H 0:=by
    rw [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric (G:=G) H z]
  unfold covariance
  rw [Matrix.transpose_mul,Matrix.transpose_mul,inv,FreeResolvent.reduce,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem received (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(vp:∀n i,Pure (F n i))(vh:∀n,shellK 2 (F n))
    (z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))
    (w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}(k:ℕ)
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(mp:∀ n i,Pure (U n i))(mh:∀ n,shellK k (U n))
    (e r:ℕ):
    Bends 0 (fun n=>reed (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) k (U (n*P.L)) e r)
      (scoop (draft (post P M).transpose (bulk P K Ñ Γ W p k e r))):=by
  apply Bends.congr (submitted P K Ñ b t g vac vp z w marked mp k e r)
  exact Eventually.of_forall fun n=>(WilsonIndependentConditionalMerPosted.original P K Ñ H Q F U k n e r
    (vh _) t (mh _) (vp _) (mp _) b (symmetric _ _ H (z n))).symm

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth k Z):
    let P:=loose A m;let K:=A.clock.kernel;let Γ:=shuttleM (conditional A N m)
    let M:=shuttleM (feedA A N m);let W:=actionW A Ñ N (m+1)
    (verseI A Ñ m N k Z).2=Blue.mix (ratioHigh A Ñ N m)
      (fun e r=>scoop (draft (post P M).transpose (bulk P K Ñ Γ W Z.2 k e r))):=by
  intro P K Γ M W
  let hist:=old A Ñ simple ratio N (m+1) finer
  unfold verseI
  apply congrArg (Blue.mix _)
  funext e r
  have mark (i j):Bends (lift (0:Site P.L)) (fun n=>Z.1 n i j) (Z.2 i j):=by
    rw [coat0];exact source.wing i j
  have appoint:=resin A N m finer
  exact (river P K Ñ Γ M W (A.blocks m 0).branches ratio appoint hist.patch k 0 mark e r).exten
    (received P K Ñ (A.blocks m 0).branches ratio appoint hist.patch (fun n=>(hist.basis n).shape)
      (fun n=>(hist.basis n).lamp) (fun n=>Bank.age_sym A N (m+1) (n*P.L))
      0 k mark source.pale source.span e r)

end YM.Integration.WilsonIndependentConditionalMerReceiver
