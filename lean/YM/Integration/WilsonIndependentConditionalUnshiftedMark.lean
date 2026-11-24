import YM.Integration.WilsonIndependentConditionalUnshiftedQuiet
import YM.Integration.WilsonIndependentConditionalFundedDraft

/-! The complete marked heat on the joint noise and held axes has a rooted
salary before the predictor and before the final projection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalUnshiftedMark
open Filter Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open scoped Topology BigOperators Classical
variable {G:Gauge}
open WilsonIndependentConditionalUnshiftedQuiet

def word (P:Patch)(U:(n:Side)→ Pal ℝ (Woods G n))(n:Side)(i:ℕ):Gen ℝ (Co n (Hinge G P.L)):=
  bend (weaveH (ratioN P.L n) G) (srCold (U (n*P.L)) 0 i)

theorem enrolled (P:Patch)(w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(i r:ℕ):
    Bends 0 (fun n=>word P U n i r) (slidesJ P 0 p i r):=by
  let I n:=weaveFine (ratioN P.L n) G
  let T n:=weaveH (ratioN P.L n) G
  apply Bends.congr (solo_flash (P:=tiles P.L (p i)) (Q:=fun n=>bend (I n) (U (n*P.L) i))
    (Pilots.one.deck (Pilots.silent (β:=Hooks G))) ((marked i r).ciphers w))
  refine Eventually.of_forall fun n=>?_
  unfold word srCold
  rw [bend_fade (I n) (T n),show allotM (I n) (T n) _=upper 1 _ from cam_chart _ _]
  rfl

def finite (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(H:FaceRow)(F:Crude G)
    (U:(n:Side)→Pal ℝ (Woods G n))(m:ℕ)(n:Side)(e:ℕ):Gen ℝ (Co n (Hinge G P.L)):=
  let J:=WilsonIndependentConditionalUnshiftedQuiet.matrix P K H n
  ∑ j∈Finset.range (m+3*e+1),bul J (abr J (WilsonIndependentConditionalUnshiftedQuiet.quiet P K Ñ F n)) (word P U n) j e

def bulk (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)
    (Γ:ropes Cover (Larvae G P.L) (Larvae G P.L))(W:Canvas G)(p:Pal ℝ (YForest G))(m:ℕ):
    Orders (Cloth (Hinge G P.L)):=
  let J:=WilsonIndependentConditionalUnshiftedQuiet.kernel P Γ
  endHeat m J (logHeat J (stellar P K Ñ 0 W) false) (slidesJ P 0 p)

theorem covered (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(vp:∀n i,Pure (F n i))
    (z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))
    (w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(mp:∀ n i,Pure (U n i))(m e r:ℕ):
    Bends 0 (fun n=>finite P K Ñ H F U m n e r) (bulk P K Ñ Γ W p m e r):=by
  let J:=WilsonIndependentConditionalUnshiftedQuiet.kernel P Γ
  let X:=WilsonIndependentConditionalUnshiftedQuiet.matrix (G:=G) P K H
  let Y n:=abr (X n) (WilsonIndependentConditionalUnshiftedQuiet.quiet P K Ñ F n)
  let V:=spurs P K Ñ Γ 0 W
  let Z:=slidesJ P 0 p
  have seed:=enrolled P w marked
  have paid:=WilsonIndependentConditionalUnshiftedQuiet.covariance P K g
  have quiet (j i r):Yields (fun n=>Y n j i r) (V j i r):=
    tide_pages paid (WilsonIndependentConditionalUnshiftedQuiet.inlet P K Ñ b t vac) j i r
  have shape:gradedSymmetric Z:=by
    intro i r
    apply (seed i r).pure (Eventually.of_forall _)
    intro n π x
    exact fade_pure (mp (n*P.L) i) _ r π ((weaveH (ratioN P.L n) G).symm ∘ x)
  have switch:=WilsonIndependentConditionalCoverHeat.original paid (WilsonIndependentConditionalUnshiftedQuiet.symmetric P K g z) quiet seed shape
  have converted:=WilsonIndependentConditionalPostedHeat.conduct J (WilsonIndependentConditionalUnshiftedQuiet.covered P K Ñ b t g vac vp z) Z m
  change Bends 0 _ (endHeat m J (logHeat J (stellar P K Ñ 0 W) false) Z e r)
  rw [←converted]
  have passed:=leaderT (s:=Finset.range (m+3*e+1)) (P:=fun n j=>bul (X n) (Y n) (word P U n) j e)
    (F:=fun j=>heap J V Z j e) (fun j _=>heap_period paid quiet seed j e r)
  have one (j):heap J V Z j e r=markHeat J V Z j e r:=congrFun (congrFun (switch j) e) r
  simpa only [endHeat,heated,Finset.sum_apply,one,finite] using passed

end YM.Integration.WilsonIndependentConditionalUnshiftedMark
