import YM.Integration.WilsonIndependentConditionalCoverPuck

/-! The normalized signed response on the nominated cover pupil. Its complete
marked input lives on the actual dated quiet, including its held scalar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentSubmittedCoverVerse
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Diagram
open Laurent Bloch Exterior Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonCoeffUV.Blue Embroider Embroider.Canvas
open scoped Classical BigOperators
variable {G:Gauge}

def before (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)
    (Γ:ropes Cover (Larvae G P.L) (Larvae G P.L))(M:ropes Cover (Larvae G P.L) (Hooks G))
    (W:Canvas G)(l:ℕ)(p:Pal ℝ (YForest G)):Pal ℝ (YForest G):=fun e=>
  sluice (endHeat l (stair (upper (β:=Hooks G) Γ 0) 0) (spurs P K Ñ Γ M W) (slidesJ P M p) e)

theorem unsummed (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(sym:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))
    (w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(pure:∀n i,Pure (U n i))(l:ℕ):
    windsT P K Ñ Γ M W l p=before P K Ñ Γ M W l p:=by
  funext e
  unfold windsT before
  apply congrArg sluice
  funext r
  simp only [Finset.sum_apply,Diagram.endHeat,Diagram.heated]
  rw [show 1+l+3*e=l+3*e+1 by omega]
  apply Finset.sum_congr rfl;intro j _
  exact congrFun (congrFun (WilsonIndependentConditionalCoverPuck.original P K Ñ b t g vac sym w marked pure j) e) r

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(Z:Era G ℝ)(source:Auth k Z):
    (verseI A Ñ m N k Z).2=Blue.mix (ratioHigh A Ñ N m)
      (before (loose A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m))
        (actionW A Ñ N (m+1)) k Z.2):=by
  unfold verseI
  apply congrArg (Blue.mix (ratioHigh A Ñ N m))
  apply unsummed _ _ _ (A.blocks m 0).branches ratio (resin A N m finer)
    (old A Ñ simple ratio N (m+1) finer).patch (fun n=>Bank.age_sym A N (m+1) (n*(loose A m).L)) 0 (U:=Z.1)
  · intro i r;rw [coat0];exact source.wing i r
  · exact source.pale

end YM.Integration.WilsonIndependentSubmittedCoverVerse
