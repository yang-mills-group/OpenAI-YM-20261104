import YM.Integration.WilsonIndependentConditionalCoverVacuum
import YM.Integration.WilsonIndependentConditionalOrdinaryCover

/-! The actual submitted source, at a fixed child on its own cover and
with its old quiet. No projection to the zero held angle is taken. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalQuietBank
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

theorem covered (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(pure:∀n i,Pure (F n i))
    (z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))(k:ℕ):
    WilsonIndependentConditionalScalarConvention.Positive (spurs P K Ñ Γ M W k)
      (logHeat (stair (upper (β:=Hooks G) Γ 0) 0) (stellar P K Ñ M W) false k):=by
  let T n:=weaveH (ratioN P.L n) G
  let I n:=weaveFine (ratioN P.L n) G
  let X (n:Side):=allotM (T n) (T n) (fillSlots (Woods G n) (mer (G:=G) P K H n))
  let V (n:Side) i:=bend (T n) (casePW (stepAt P K n) Ñ (teller G P K Q n) (F (n*P.L)) i)
  have hV (i r):Yields (fun n=>V n i r) (stellar P K Ñ M W i r):=
    star_pages (P:=P) (W:=F) (Z:=W) (T:=teller G P K Q) K g.mark t b i r (vac i r)
  have smooth:gradedSymmetric (stellar P K Ñ M W):=by
    intro i r
    apply (hV i r).sym
    refine Eventually.of_forall fun n π x=>?_
    exact pack_pure (stepAt P K n) t b (pure (n*P.L)) i r π ((T n).symm∘x)
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
  exact WilsonIndependentConditionalCoverVacuum.original hv Ksym hV smooth k

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N:ℕ}(finer:m<N)(k:ℕ):
    let P:=loose A m;let K:=A.clock.kernel;let Γ:=shuttleM (conditional A N m)
    let M:=shuttleM (feedA A N m);let W:=actionW A Ñ N (m+1)
    WilsonIndependentConditionalScalarConvention.Positive (spurs P K Ñ Γ M W k)
      (logHeat (stair (upper (β:=Hooks G) Γ 0) 0) (stellar P K Ñ M W) false k):=by
  let h:=old A Ñ simple ratio N (m+1) finer
  exact covered _ _ _ (A.blocks m 0).branches ratio (resin A N m finer) h.patch
    (fun n=>(h.basis n).shape) (fun n=>Bank.age_sym A N (m+1) (n*(loose A m).L)) k

end YM.Integration.WilsonIndependentConditionalQuietBank
