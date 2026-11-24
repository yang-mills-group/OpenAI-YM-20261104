import YM.Integration.WilsonIndependentMatchedTopWard
import YM.Next.WARD_BIN.Stencils

/-! Matrix calculus for the single genuine link left after the reflected
link has left the support. Both origins remain in the physical Ward test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardSingleSlope
open Function Lattice Wilson WardBin FormalOPE.RG10.InversionWard
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]

def move (b:Edge (Site n))(M:ArrayOf G n)(v:G.Color) : ArrayOf G n :=
  fun i=>if i=b then G.mat (G.lieExp v)*M i else M i

theorem exact_move (b:Edge (Site n))(U:Config G n)(v:G.Color) :
    move b (image U) v=image (WardBin.slide b U v) := by
  funext i
  by_cases h:i=b
  · subst i
    simp [move,image,WardBin.slide,G.mat_mul]
  · simp [move,image,WardBin.slide,h]

theorem smooth (b:Edge (Site n)) : ContDiff ℝ ∞ (uncurry (move (G:=G) b)) := by
  apply contDiff_pi.mpr
  intro i
  unfold uncurry move
  have ha:ContDiff ℝ ∞ fun x:ArrayOf G n × G.Color=>x.1 i:=(contDiff_apply ..).comp contDiff_fst
  split
  · exact ((G.exp_jet.of_le le_top).comp contDiff_snd).mul ha
  · exact ha

def tangent (b:Edge (Site n))(f:Config G n→E)(U:Config G n) :=
  fderiv ℝ (fun v=>f (WardBin.slide b U v)) 0

theorem line (b:Edge (Site n)){f:Config G n→E}(paid:Proxy f)(U:Config G n) :
    ContDiff ℝ ∞ (fun v=>f (WardBin.slide b U v)) := by
  obtain ⟨A,hA,rfl⟩:=paid
  simp_rw [Function.comp_apply,←exact_move]
  exact (hA.comp (smooth b)).comp (f:=fun v=>(image U,v)) (contDiff_const.prodMk contDiff_id)

theorem field (b:Edge (Site n)){f:Config G n→E}(paid:Proxy f) : Proxy (tangent b f) := by
  obtain ⟨A,hA,rfl⟩:=paid
  refine ⟨fun M=>fderiv ℝ (fun v=>A (move b M v)) 0,
    ContDiff.fderiv (hA.comp (smooth b)) (g:=fun _=>0) contDiff_const (by simp),?_⟩
  funext M
  unfold tangent
  simp_rw [Function.comp_apply,exact_move]

theorem scalar (b:Edge (Site n)){f:Config G n→E}(paid:Proxy f)(a:G.Color) : Proxy (slope b a f) := by
  have hit:= (field b paid).after (fun L=>L a) (ContinuousLinearMap.apply ℝ E a).contDiff
  convert hit using 1
  funext U
  have he : HasDerivAt (fun t:ℝ=>t • a) a 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a
  exact (((line b paid U).differentiable (by simp) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 he (by simp)).deriv

end YM.Integration.WilsonIndependentWardSingleSlope
