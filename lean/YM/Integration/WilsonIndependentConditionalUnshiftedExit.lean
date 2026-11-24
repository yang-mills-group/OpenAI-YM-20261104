import YM.Integration.WilsonIndependentConditionalUnshiftedMark

/-! Fixed-child thermodynamic return of the unshifted marked heat followed
by the actual harmonic predictor. Every positive and zero angular row
has an absolutely funded passage through the posterior. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalUnshiftedExit
open Filter Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalUnshiftedMark
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open scoped Topology BigOperators Classical
variable {G:Gauge}

def post (P:Patch)(M:ropes Cover (Larvae G P.L) (Hooks G)):ropes Cover (Hinge G P.L) (Hinge G P.L):=
  stair (upper 0 M) ladder

def ends (P:Patch)(K:KernelChoices)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)(n:Side):
    ropes (Site n) (Hinge G P.L) (Hinge G P.L):=
  let I:=weaveFine (ratioN P.L n) G
  stair (upper 0 (allotM I (Equiv.refl _) (teller G P K Q n))) ladder

theorem predictor (P:Patch)(K:KernelChoices){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    (g:PaintKit P K G H Q Γ M):Pilots (ends P K Q) (post P M):=
  ((Pilots.silent (α:=Larvae G P.L)).deck g.mark).deck' ladder_fold

theorem honest (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(H:FaceRow)(F:Crude G)
    (U:(n:Side)→ Pal ℝ (Woods G n))(p:∀n i,Pure (U n i))(m n e): Pure (finite P K Ñ H F U m n e):=by
  apply pure_sum
  intro j _
  apply pure_bul
  intro i r π x
  exact fade_pure (p (n*P.L) i) _ r π ((weaveH (ratioN P.L n) G).symm ∘ x)

theorem submitted (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(vp:∀n i,Pure (F n i))
    (z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))
    (w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(mp:∀ n i,Pure (U n i))(m e r:ℕ):
    Bends 0 (fun n=>scoop (fade (ends P K Q n) (finite P K Ñ H F U m n e) r))
      (scoop (draft (post P M).transpose (bulk P K Ñ Γ W p m e r))):=by
  have word:=WilsonIndependentConditionalUnshiftedMark.covered P K Ñ b t g vac vp z w marked mp m e r
  have hm:=predictor P K g
  have sym:=word.pure (Eventually.of_forall fun n=>honest P K Ñ H F U mp m n e r)
  rw [WilsonIndependentConditionalFundedDraft.original (capit hm) word sym,transpose_transpose]
  exact (solo_flash hm word).scooped

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth k Z)(e r:ℕ):
    let P:=loose A m;let K:=A.clock.kernel;let H:=freeForms A N (m+1)
    let Γ:=shuttleM (conditional A N m);let M:=shuttleM (feedA A N m);let W:=actionW A Ñ N (m+1)
    let F:Crude G:=(story A Ñ N (m+1)).1
    Bends 0 (fun n=>scoop (fade (ends P K (roam A N m) n) (finite P K Ñ H F Z.1 k n e) r))
      (scoop (draft (post P M).transpose (bulk P K Ñ Γ W Z.2 k e r))):=by
  let h:=old A Ñ simple ratio N (m+1) finer
  apply submitted _ _ _ (A.blocks m 0).branches ratio (resin A N m finer) h.patch
      (fun n=>(h.basis n).shape) (fun n=>Bank.age_sym A N (m+1) (n*(loose A m).L)) 0 _ source.pale
  intro i s
  rw [coat0]
  exact source.wing i s

end YM.Integration.WilsonIndependentConditionalUnshiftedExit
