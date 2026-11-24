import YM.Integration.WilsonPhysicalHistoryRetainedSpringTaylor

/-! The finite polynomial in each rooted remainder consists of the actual
derivatives of its compact Wilson field along the submitted angular ray. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Wilson Finset Work.F02
open FundedCurvatureRayTaylor WilsonMeasuredPathTaylor
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}

theorem atom_ray_coefficient (a : Atom G k) (x : Site n) (v : Directions G n) (r : ℕ) :
    CubicMatch.term r (fun t : ℝ=>(a.unmasked (field v t) x : ℂ)) =
      ∑ b,(a.coeff b) • CubicMatch.term r (read v x (letters a b)) := by
  have printed : (fun t : ℝ=>(a.unmasked (field v t) x : ℂ)) =
      fun t=>∑ b,a.coeff b • read v x (letters a b) t := by
    funext t
    simpa only [Complex.real_smul] using evaluated a x v t
  have smooth (b : Fin k→G.ColorIndex) := (read_smooth v x (letters a b)).contDiffAt (x:=0)
  rw [printed,CubicMatch.term_sum (s:=Finset.univ) (g:=fun b t=>a.coeff b • read v x (letters a b) t)
    (fun b _=>((smooth b).const_smul (a.coeff b)).of_le le_top)]
  exact Finset.sum_congr rfl fun b _=>CubicMatch.term_scaled _ (smooth b)

theorem atom_ray_polynomial (a : Atom G k) (x : Site n) (v : Directions G n) (q : ℕ) (t : ℝ) :
    polynomial a x v q t=∑ r ∈ range (q+1),
      t^r • CubicMatch.term r (fun u : ℝ=>(a.unmasked (field v u) x : ℂ)) := by
  have cut (b : Fin k→G.ColorIndex) : jet (read v x (letters a b)) q t=
      ∑ r∈range (q+1),t^r • CubicMatch.term r (read v x (letters a b)) := by
    unfold jet CubicMatch.term
    apply Finset.sum_congr rfl
    intro r _
    rw [smul_smul,mul_comm (t^r)]
  simp only [polynomial,cut,←Complex.real_smul,atom_ray_coefficient,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact Finset.sum_congr rfl fun _ _=>smul_comm _ _ _

theorem polynomial_continuous (a : Atom G k) (x : Site n) (q : ℕ) (t : ℝ) :
    Continuous (fun v : Directions G n=>polynomial a x v q t) := by
  let F : Directions G n→ℂ:=fun v=>(a.unmasked (field v 1) x : ℂ)
  have localG : ContDiffAt ℝ ω F 0 := by
    have hull : F=fun v=>atomExt a x (physical (field v 1)):=funext fun v=>(atomExt_physical ..).symm
    rw [hull]
    apply ((atomExt_contDiff a x).restrict_scalars ℝ).contDiffAt.comp _ (physical_contDiffAt ?_)
    intro e
    simp only [field,one_smul]
    exact G.exp_jet.contDiffAt.comp _ (by fun_prop)
  have ray (v : Directions G n) : (fun u : ℝ=>(a.unmasked (field v u) x:ℂ))=fun u=>F (u • v) := by
    funext u
    have eq : field (u • v) (1:ℝ)=field v u := by
      funext e
      change G.lieExp ((1:ℝ) • (u • v) e)=G.lieExp (u • v e)
      rw [one_smul]; rfl
    exact congrArg (fun U : Config G n=>(a.unmasked U x:ℂ)) eq.symm
  simp_rw [atom_ray_polynomial,ray]
  apply continuous_finsetSum
  intro r _
  have hr : ContDiffAt ℝ r F 0:=localG.of_le le_top
  simp_rw [CubicMatch.term_ray hr]
  exact ((Tensor.coeff F r 0).cont.comp (continuous_pi fun _=>(continuous_id (X:=Directions G n)))).const_smul (t^r)

end YM.Integration.OriginalMarkedRunAction
