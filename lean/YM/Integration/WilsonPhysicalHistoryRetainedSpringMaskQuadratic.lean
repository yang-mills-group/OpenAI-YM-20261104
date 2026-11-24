import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskFace
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskLinear

/-! The whole quadratic coefficient retains both the direct Wilson four-link
trace and every ordered pair of paths in the true kinetic operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Stationary MeasureTheory OPE.Therm
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

def maskedSecondAt (K : PathData G) (c : Clip) (p : BudgetPoint) (x : Site n) (U : Config G n) : ℝ:=
  Patch.average fun s : Signed=>let v:=Song.splay n (s,x)
                                maskedFace K c p v U+maskedGram K c p v U

theorem face_shifted (s : Signed) (x : Site n) (U : Config G n) :
    faceSeat G (Song.splay n (s,x)) U=∑a : PlaqAxes,G.price (faceValue (pull s 0 U) (x,a)) := by
  have he : (Song.splay n (s,x)).view U=translate x (pull s 0 U) := by
    rw [←pull_one,pull_pull,mul_one,affine,add_zero];rfl
  unfold faceSeat
  rw [he]
  apply sum_congr rfl
  intro a _
  rw [AnalyticBridge.GaussianFieldAlignment.Channels.translated_face]
  change G.price (faceValue (pull s 0 U) (0+x,a))=_
  rw [zero_add]

def faceMaskCap (_G : Gauge) (c : Clip) : ℝ:=(Fintype.card PlaqAxes:ℝ)*(|c.direct| *2)

def quadraticMaskCap (G : Gauge) (c : Clip) (D : ℝ) : ℝ:=faceMaskCap G c+4*gramCost G D

def quadraticMaskRent (G : Gauge) (c : Clip) (p : BudgetPoint) (σ D : ℝ) : ℝ:=
  let b:=((2*p.B+1)^4:ℕ)
  faceMaskCap G c*b+(gramCost G D)*4*(5+b+σ⁻¹)

theorem spring_mask_quadratic (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per (K : PathData G) (c : Clip) (σ D Λ : ℝ),0<σ→
      K.Bounds c σ D Λ→∀ (x : Site (R.family.side j per)),
      let p:=(R.family.path.rep N per j).p
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedSecondAt K c p x U-secondAt c K x U
      Measurable f ∧ (∀U,‖f U‖≤quadraticMaskCap G c D) ∧
        (∫U,‖f U‖ ∂scene R.family.path N per j)≤quadraticMaskRent G c p σ D*fee := by
  filter_upwards [spring_mask_face R simple heat q,spring_mask_gram R simple heat q] with j face gram N live per K c σ D Λ hs path x p fee f
  let n:=R.family.side j per
  let μ:=scene R.family.path N per j
  letI : IsProbabilityMeasure μ:=probability R.makes.wilson live
  let v (s : Signed):=Song.splay n (s,x)
  let F (s : Signed) (U : Config G n):=(maskedFace K c p (v s) U-c.direct*faceSeat G (v s) U)+
    (maskedGram K c p (v s) U-∑'i,(gramEntries K i).unmasked ((v s).view U) 0)
  have same : f=fun U=>Patch.average (fun s=>F s U) := by
    funext U
    dsimp only [f,maskedSecondAt,F,v]
    rw [gram_at K path x U]
    dsimp only [facePriceAt,sitePacket,Patch.average]
    simp_rw [shifted_atom,face_shifted]
    simp only [sum_add_distrib,sum_sub_distrib,←mul_sum]
    ring
  rw [same]
  apply mean_mask
  intro s
  have joint:=add_mask μ (face N live per K c (v s)) (gram N live per K c σ D Λ hs path p rfl (v s))
  refine ⟨joint.1,fun U=>(joint.2.1 U).trans_eq (by unfold quadraticMaskCap faceMaskCap;ring),joint.2.2.trans_eq ?_⟩
  dsimp only [quadraticMaskRent,faceMaskCap]
  push_cast
  ring

end YM.Integration.OriginalMarkedRunAction
