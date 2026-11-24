import YM.Integration.WilsonMacroscopicRichDescentPosterior
import YM.RGComparison.Core16.Savings

/-! Both terms in the conditional covariance on the very same original
interacting history, for the actual upper registered grade-four fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairPosterior
open Filter Function Set MeasureTheory Lattice RG Wilson OPE OPE.Therm Push.GridApprox
open RGComparison.Core16 PhysicalNext.Repeat.Legato WilsonMacroscopicForwardTransfer
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p u : ℕ} (T : Slices R.family.path.levels p) (h : u≤N)

def held (X : Config G (R.family.side N p)→ℂ) (V : Config G (R.family.side u p)) : ℂ :=
  (traversal T h).conditioned (line R.family.path p u N) X V

private theorem paid (X : Config G (R.family.side N p)→ℂ) (cont : Continuous X) :
    Integrable (held R T h X) (scene R.family.path N p u) ∧
      (∫V,held R T h X V ∂scene R.family.path N p u)=∫U,X U ∂scene R.family.path N p N := by
  letI : IsProbabilityMeasure (scene R.family.path N p N):=probability R.makes.wilson le_rfl
  have usable : Integrable X (scene R.family.path N p N):=
    cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have known (V):exterior (C:=R.family) (N:=N) h X V=held R T h X V:=
    WilsonMacroscopicRichDescentPosterior.measured R T h X V
  have bound:=WilsonMacroscopicForwardTransfer.contract (C:=R.family) R.makes h (le_refl N) X usable
  have joint:=WilsonMacroscopicForwardTransfer.joint (C:=R.family) R.makes h (le_refl N) X usable
    (fun _=>(1:ℂ)) (show Envelope (fun _:Config G (R.family.side u p)=>(1:ℂ)) from
      ⟨measurable_const,1,by simp⟩)
  refine ⟨?_,?_⟩
  · rw [← funext known]
    exact bound.1
  · simpa only [known,backTo_const,mul_one] using joint

theorem original (a b : R.family.label 4) (x y : Site (R.family.side N p)) :
    let X:=R.family.O N p a x
    let Y:=R.family.O N p b y
    let μ:=scene R.family.path N p N
    let ν:=scene R.family.path N p u
    let A:=held R T h X
    let B:=held R T h Y
    let pair:=held R T h (fun U=>X U*Y U)
    (∫U,X U*Y U ∂μ)-(∫U,X U ∂μ)*(∫U,Y U ∂μ)=
      (∫V,pair V-A V*B V ∂ν)+((∫V,A V*B V ∂ν)-(∫V,A V ∂ν)*(∫V,B V ∂ν)) := by
  intro X Y μ ν A B pair
  have xcont : Continuous X:=R.family.continuousO ..
  have ycont : Continuous Y:=R.family.continuousO ..
  obtain ⟨xa,xread⟩:=paid R T h X xcont
  obtain ⟨yb,yread⟩:=paid R T h Y ycont
  obtain ⟨both,total⟩:=paid R T h (fun U=>X U*Y U) (xcont.mul ycont)
  obtain ⟨K,originalBound⟩:=isCompact_univ.exists_bound_of_continuousOn xcont.continuousOn
  have envelope (V:Config G (R.family.side u p)):‖A V‖≤K:=
    Descent.conditioned_bound (traversal_ok T h) _ (fun U=>originalBound U (Set.mem_univ _)) xcont V
  have joint : Integrable (fun V=>A V*B V) ν:=yb.bdd_mul xa.aestronglyMeasurable (Eventually.of_forall envelope)
  rw [integral_sub both joint,total,xread,yread]
  abel

end YM.Integration.WilsonInvariantActionPairPosterior
