import YM.Integration.WilsonIndependentConditionalCoverHeat
import YM.Integration.WilsonIndependentConditionalOrdinaryCover

/-! The actual submitted source, at a fixed child on its own cover and
with its old quiet. No projection to the zero held angle is taken. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverPuck
open Filter Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem sym {c f:Side}(S:StepData c f)(T:Forest S.ratio)(H:FaceRow)(z:(H.acts f).transpose=H.acts f):
    (covariance G S T H).transpose=covariance G S T H:=by
  have inv:(treeInverse G S T H 0).transpose=treeInverse G S T H 0:=by
    rw [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric (G:=G) H z]
  unfold covariance
  rw [Matrix.transpose_mul,Matrix.transpose_mul,inv,FreeResolvent.reduce,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem original (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀ i r,Yields (fun n=>F n i r) (W i r))(z:∀ n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))
    (w:Site P.L){p:Pal ℝ (YForest G)}{U:(n:Side)→ Pal ℝ (Woods G n)}
    (marked:∀i r,Bends (lift w) (fun n=>U n i r) (p i r))(pure:∀n i,Pure (U n i))(k:ℕ):
    puck P K Ñ Γ M W p k=
      markHeat (stair (upper (β:=Hooks G) Γ 0) 0) (spurs P K Ñ Γ M W) (slidesJ P M p) k:=by
  let T n:=weaveH (ratioN P.L n) G
  let I n:=weaveFine (ratioN P.L n) G
  let Y (n:Side) j v:=bend (T n) (xray (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) j v)
  let X (n:Side):=allotM (T n) (T n) (fillSlots (Woods G n) (mer (G:=G) P K H n))
  let Z (n:Side) i:=bend (T n) (srCold (U (n*P.L)) (teller G P K Q n) i)
  have he i r:Bends 0 (fun n=>Z n i r) (slidesJ P M p i r):=by
    apply Bends.congr (solo_flash (P:=tiles P.L (p i)) (Q:=fun n=>bend (I n) (U (n*P.L) i)) (Pilots.one.deck g.mark) ((marked i r).ciphers w))
    refine Eventually.of_forall fun n=>?_
    unfold Z srCold;rw [bend_fade (I n) (T n),show allotM (I n) (T n) _=upper 1 _ from cam_chart _ _]
  let J:=stair (α:=Larvae G P.L) (β:=Hooks G) (upper Γ 0) (0:ropes Cover (Hooks G) (Hinge G P.L))
  have hv:Pilots X J:=by
    rw [show X=fun n:Side=>stair (upper (allotM (I n) (I n) (mer (G:=G) P K H n)) (β:=Hooks G) 0) (β:=Hooks G) 0 from funext fun n=>lamp_chart ..]
    exact ((g.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))
  have hs (n:Side):(X n).transpose=X n:=by
    unfold X allotM
    rw [transpose_submatrix,fillSlots,Matrix.fromBlocks_transpose,sym (stepAt P K n) (xree P K n) H (z n)]
    simp
  have Ksym:J.transpose=J:=by
    ext x y
    apply tendsto_nhds_unique (hv.point y x)
    apply (hv.point x y).congr
    intro n
    exact congrFun (congrFun (hs n).symm _) _
  have ps:gradedSymmetric (slidesJ P M p):=by
    intro i r
    apply (he i r).pure (Eventually.of_forall _)
    intro n π x
    exact fade_pure (pure (n*P.L) i) _ r π ((T n).symm∘x)
  exact WilsonIndependentConditionalCoverHeat.original hv Ksym (spurs_enter P K Ñ H F Q b t vac g) he ps k

end YM.Integration.WilsonIndependentConditionalCoverPuck
