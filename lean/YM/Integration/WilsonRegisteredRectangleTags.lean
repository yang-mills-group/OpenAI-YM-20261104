import YM.Integration.WilsonRegisteredRectangleFactors

/-! The authentic Wilson transition after summing its bond tags.
Only the globally shared site tags that actually use an axial frame enter the result. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleTags
open Function Finset Lattice RG Wilson MeasureTheory
open scoped Classical
variable {G:Gauge}{c f:Side}(S:StepData c f)
def site (U:Config G f)(a:S.SitesChoice)(x:Site c):ℝ:=
  S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) (a x)
def edge (β:ℝ)(U:Config G f)(W:Config G c)(a:S.SitesChoice)(e:Edge (Site c))(b:S.patch.Points):ℝ:=
  S.patch.predictorMass S.kernel (S.connector U a e) b*
    ((S.penaltyZ β G)⁻¹*S.penaltyWeight β (W e*(S.patch.predict S.kernel (S.connector U a e) b)⁻¹))
def branch (β:ℝ)(U:Config G f)(W:Config G c)(a:S.SitesChoice):ℝ:=
  (∏x,site S U a x)*∏e,∑b,edge S β U W a e b

theorem measured (β:ℝ)(U:Config G f)(W:Config G c):S.density β U W=∑a:S.SitesChoice,branch S β U W a:=by
  unfold StepData.density
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl;intro a _
  unfold branch
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro b _
  dsimp [StepData.likelihood,StepData.noise,StepData.prediction,site,edge]
  simp only [Finset.prod_mul_distrib];ring

def kept (U:Config G f)(source fixed:S.SitesChoice):S.SitesChoice:=fun x=>
  if S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) U) then fixed x else source x

theorem frames (U:Config G f)(a fixed:S.SitesChoice)(x:Site c):S.frames U (kept S U a fixed) x=S.frames U a x:=by
  by_cases h:S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) U)
  · simp only [StepData.frames,Patch.frame,if_pos h]
  · simp only [StepData.frames,kept,if_neg h]

theorem connectors (U:Config G f)(a fixed:S.SitesChoice)(e:Edge (Site c)):
    S.connector U (kept S U a fixed) e=S.connector U a e:=by
  funext b
  simp only [StepData.connector,frames]

theorem observed (β:ℝ)(U:Config G f)(W:Config G c)(a fixed:S.SitesChoice):
    branch S β U W (kept S U a fixed)=branch S β U W a:=by
  have loc(x:Site c):site S U (kept S U a fixed) x=site S U a x:=by
    by_cases h:S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) U)
    · simp only [site,Patch.frameMass,if_pos h]
    · simp only [site,kept,if_neg h]
  simp only [branch,loc,edge,connectors]

theorem original (β:ℝ)(U:Config G f)(W:Config G c)(fixed:S.SitesChoice):
    S.density β U W=∑a:S.SitesChoice,branch S β U W (kept S U a fixed):=by
  simp only [observed,measured]

end YM.Integration.WilsonRegisteredRectangleTags
