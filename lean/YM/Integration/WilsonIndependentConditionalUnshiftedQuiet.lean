import YM.Integration.WilsonIndependentConditionalPostedHeat

/-! Positive-rank unmarked heat on the original selected thermodynamic
faculty before applying its harmonic mean. The covariance, unmarked action,
and scalar-vs-intensive convention are fixed at the actual dated entrance. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalUnshiftedQuiet
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


def matrix (P:Patch)(K:KernelChoices)(H:FaceRow)(n:Side):ropes (Site n) (Hinge G P.L) (Hinge G P.L):=
  let T:=weaveH (ratioN P.L n) G
  allotM T T (fillSlots (Woods G n) (mer (G:=G) P K H n))

def kernel (P:Patch)(Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)):ropes Cover (Hinge G P.L) (Hinge G P.L):=
  stair (upper Γ 0) 0

def quiet (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(F:Crude G)(n:Side)(i:ℕ):Gen ℝ (Co n (Hinge G P.L)):=
  bend (weaveH (ratioN P.L n) G) (casePW (stepAt P K n) Ñ 0 (F (n*P.L)) i)

theorem covariance (P:Patch)(K:KernelChoices){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    (g:PaintKit P K G H Q Γ M):Pilots (matrix P K H) (kernel P Γ):=by
  let I n:=weaveFine (ratioN P.L n) G
  rw [show matrix (G:=G) P K H=fun n:Side=>
        stair (upper (allotM (I n) (I n) (mer (G:=G) P K H n)) (β:=Hooks G) 0) (β:=Hooks G) 0
      from funext fun n=>by unfold matrix;exact lamp_chart (ratioN P.L n) _]
  exact ((g.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))

theorem symmetric (P:Patch)(K:KernelChoices){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    (g:PaintKit P K G H Q Γ M)(z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L)):
    (kernel P Γ).transpose=kernel P Γ:=by
  have h:=covariance P K g
  have adj (n:Side):(matrix (G:=G) P K H n).transpose=matrix P K H n:=by
     unfold matrix allotM
     rw [transpose_submatrix,fillSlots,Matrix.fromBlocks_transpose,sym (stepAt P K n) (xree P K n) H (z n)]
     simp
  ext x y
  apply tendsto_nhds_unique (h.point y x)
  apply (h.point x y).congr
  intro n
  exact congrFun (congrFun (adj n).symm _) _

theorem inlet (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){W:Canvas G}{F:Crude G}
    (b:P.Branches K G)(t:LocalRatio Ñ)(vac:∀i r,Yields (fun n=>F n i r) (W i r))(i r:ℕ):
    Yields (fun n=>quiet P K Ñ F n i r) (stellar P K Ñ 0 W i r):=by
  exact star_pages (P:=P) (W:=F) (Z:=W) (T:=fun _=>0) K Pilots.silent t b i r (vac i r)

theorem covered (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H Q}
    {Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}
    {W:Canvas G}{F:Crude G}(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M)
    (vac:∀i r,Yields (fun n=>F n i r) (W i r))(pure:∀n i,Pure (F n i))
    (z:∀n:Side,(H.acts (n*P.L)).transpose=H.acts (n*P.L))(k:ℕ):
    WilsonIndependentConditionalScalarConvention.Positive (spurs P K Ñ Γ 0 W k)
      (logHeat (kernel P Γ) (stellar P K Ñ 0 W) false k):=by
  have incoming:=inlet P K Ñ b t vac
  have smooth:gradedSymmetric (stellar P K Ñ 0 W):=by
    intro i r
    apply (incoming i r).sym
    exact Eventually.of_forall fun n π x=>pack_pure (stepAt P K n) t b (pure (n*P.L)) i r π
        ((weaveH (ratioN P.L n) G).symm ∘ x)
  exact WilsonIndependentConditionalCoverVacuum.original (covariance P K g) (symmetric P K g z) incoming smooth k

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N:ℕ}(finer:m<N)(k i r:ℕ)(hr:0<r):
    let P:=loose A m;let K:=A.clock.kernel;let H:=freeForms A N (m+1)
    let Γ:=shuttleM (conditional A N m);let W:=actionW A Ñ N (m+1)
    let F:Crude G:=(story A Ñ N (m+1)).1
    Yields (fun n=>abr (matrix P K H n) (quiet P K Ñ F n) k i r)
      (logHeat (kernel P Γ) (stellar P K Ñ 0 W) false k i r):=by
  let h:=old A Ñ simple ratio N (m+1) finer
  let g:=resin A N m finer
  have eq:=covered _ _ _ (A.blocks m 0).branches ratio g h.patch
    (fun n=>(h.basis n).shape) (fun n=>Bank.age_sym A N (m+1) (n*(loose A m).L)) k i r hr
  dsimp only
  exact eq ▸ tide_pages (covariance _ _ g) (inlet _ _ _ (A.blocks m 0).branches ratio h.patch) k i r

end YM.Integration.WilsonIndependentConditionalUnshiftedQuiet
