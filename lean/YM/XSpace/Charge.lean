import YM.XSpace.BCH

/-!
# Lift face and path through degree two

Orbit PT application at finite and expanding regulator incl infinite lattice stencil,
no harmonic conditions used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Lattice Filter Function RG Drift
open scoped Topology BigOperators
variable {G : Gauge} {R K : Type*} [AddCommGroup R] [One R] [Group K]
abbrev Edges2 (R : Type*) := Edge (Four R)
abbrev LogLinks (R : Type*) (G : Gauge) := Links R G.Color

lemma carries (u : ℝ → Links R G.El) (A : Links R (Drift G)) (h : ∀ e, Fits (fun t=> u t e) (A e)) (w : Walk) (x : Four R) : Fits (fun t=> travel (u t) x w) (travel A x w):=by
  induction w generalizing x with
  | nil => exact Fits.unit _
  | cons d w ih => simp only [travel]; refine Fits.product ?_ (ih _)
                   simp only [Step.read]; split_ifs
                   exact (h _).inverse
                   exact h _
lemma carries_face (u : ℝ → Links R G.El) (A : Links R (Drift G)) (h : ∀ e, Fits (fun t=> u t e) (A e)) (p : Face R) : Fits (fun t=> faceValue (u t) p) (faceValue A p):= carries _ _ h _ _

private def sign (d : Step) : ℝ := if d.neg then -1 else 1
def touch (x : Four R) (d : Step) : LogLinks R G→ₗ[ℝ] G.Color:= sign d • LinearMap.proj (d.used x)
lemma touch_pos (x : Four R) (i : Axis) (A : LogLinks R G): touch x (posDir i) A=A (x,i):=one_smul ℝ _
lemma touch_neg (x : Four R) (i : Axis) (A : LogLinks R G): touch x (negDir i) A= -A (x-step i,i):= neg_one_smul ℝ _

def tallyPath (x : Four R) : Walk → LogLinks R G→ₗ[ℝ] G.Color
| []=> 0
| d::w=> touch x d+tallyPath (x+d.vec) w

def duo (A Y : LogLinks R G) : Links R (Drift G):=fun e=>⟨A e,Y e⟩
abbrev native (A : LogLinks R G) := duo A 0
lemma touch_a (A Y : LogLinks R G) (x : Four R) (d : Step) : (d.read (duo A Y) x).a=touch x d A:=by cases d with | mk i h=> cases h; exact (touch_pos ..).symm; exact (touch_neg ..).symm
lemma touch_c (A Y : LogLinks R G) (x : Four R) (d : Step) : (d.read (duo A Y) x).c=touch x d Y:=by cases d with | mk i h=> cases h; exact (touch_pos ..).symm; exact (touch_neg ..).symm
lemma trip_a (A Y : LogLinks R G) (x : Four R) (w : Walk) : (travel (duo A Y) x w).a=tallyPath x w A:=by
  induction w generalizing x <;> simp_all [travel,tallyPath,touch_a]
lemma trip_c (A Y : LogLinks R G) (x : Four R) (w : Walk) : (travel (duo A Y) x w).c=(travel (native A) x w).c+tallyPath x w Y:=by
  induction w generalizing x <;> simp_all only [travel,tallyPath,c_one,LinearMap.zero_apply,add_zero,c_mul,trip_a,touch_a,native, LinearMap.add_apply,touch_c,map_zero]; abel

def linearFace (p : Face R) := tallyPath (G:=G) p.1 (square p.2.val.1 p.2.val.2)
def acc (p : Face R) (A : LogLinks R G) := (faceValue (native A) p).c
lemma face_a (p : Face R) (A Y : LogLinks R G) : (faceValue (duo A Y) p).a= linearFace p A:= trip_a ..
lemma face_c (p : Face R) (A Y : LogLinks R G) : (faceValue (duo A Y) p).c= acc p A + linearFace p Y:= trip_c ..

def diagnostic (p : Face R) (A : LogLinks R G):=inner ℝ (linearFace p A) (acc p A)
lemma angular (p : Face R) (A : LogLinks R G): linearFace p A=A (p.1,p.2.val.1)+A (p.1+step p.2.val.1,p.2.val.2) - A (p.1+step p.2.val.2,p.2.val.1)- A (p.1,p.2.val.2):=by
  simp [linearFace,tallyPath,square,touch_pos,touch_neg]; rw [add_right_comm p.1 (step p.2.val.1),add_sub_cancel_right,add_neg_cancel_right,add_sub_cancel_right]; abel

lemma diagnostic_price (p : Face R) (u : ℝ → Links R G.El) (A : LogLinks R G) (h : ∀ e, Fits (fun t=>u t e) (native A e)) : CubicMatch.term 3 (fun t=> G.price (faceValue (u t) p))= diagnostic p A:=by
  unfold diagnostic; rw [← face_a p A (0:LogLinks R G)]
  exact (carries_face u (native A) h p).price

/-- pull back a scalar gauge tangent including all colors. -/
def grad : (Four R → G.Color) →ₗ[ℝ] LogLinks R G:= LinearMap.pi (R:=ℝ) fun e : Edges2 R=> LinearMap.proj (e.1+step e.2) - (LinearMap.proj e.1 : (Four R → G.Color) →ₗ[ℝ] G.Color)
lemma grad_at (e : Edges2 R) (v : Four R → G.Color): grad v e=v (e.1+step e.2)-v e.1:=rfl

def rLink (v : Four R→G.Color) : LogLinks R G →ₗ[ℝ] LogLinks R G:= LinearMap.pi fun e=> -(G.ad ((1/2:ℝ) • (v (e.1+step e.2)+v e.1)) ∘ₗ LinearMap.proj e)
lemma r_at (v : Four R→G.Color) (A : LogLinks R G) (e) : rLink v A e=G.ad (A e) ((1/2:ℝ) • (v (e.1+step e.2)+v e.1)):= (ad_swap ..).symm

def extra (v : Four R→ G.Color) : LogLinks R G := fun e=> -(1/2:ℝ) • G.ad (v e.1) (v (e.1+step e.2))
lemma gauge_paths (t : ℝ) (v : Four R → G.Color) (A : LogLinks R G) : Lattice.gauge (fun x=>(⟨-(t • v x),0⟩:Drift G)) (native A)= duo (A+t • grad v) (t • rLink v A+t^2 • extra v):=by
  funext e; apply Drift.ext <;> simp only [Lattice.gauge,a_mul,c_mul,a_inv,c_inv,neg_neg,duo,native,Pi.add_apply,Pi.smul_apply,grad_at,r_at,Pi.zero_apply]
  · simp only [smul_sub]; abel
  unfold extra; simp only [map_smul,map_neg,map_add,LinearMap.neg_apply, LinearMap.add_apply,LinearMap.smul_apply]
  rw [ad_swap (v e.1)]; module
lemma gauge_acc (t : ℝ) (v : Four R → G.Color) (A : LogLinks R G) (p : Face R) :
    acc p (A+t • grad v) = acc p A + G.ad (linearFace p A) (t • v p.1)- linearFace p (t • rLink v A+t^2 • extra v):=by
  rw [eq_sub_iff_add_eq,← face_c,← gauge_paths,face_gauge,conjugate, ← face_a p A (0: LogLinks R G)]; simp [acc,native,ad_swap (v p.1)]
@[simp] lemma face_grad (p : Face R) (v : Four R → G.Color) : linearFace p (grad v)=0:=by
  rw [angular]; simp only [grad_at]; rw [add_right_comm p.1]; abel
-- hence ⟨(curl A)', acc...⟩ has derivative mandated by the quadratic pairing
lemma gauge_cubic (t : ℝ) (v : Four R → G.Color) (A : LogLinks R G) (p : Face R) :
    diagnostic p (A+t • grad v)= diagnostic p A - inner ℝ (linearFace p A) (linearFace p (t • rLink v A+t^2 • extra v)):=by rw [diagnostic,diagnostic,gauge_acc]; rw [map_add,map_smul,face_grad,smul_zero,add_zero,inner_sub_right,inner_add_right,ad_swap (linearFace p A),inner_neg_right,ad_e]; ring
-- constants: curvature second is exactly nonabelian completion
lemma constant_will (A : Axis → G.Color) (p : Face R) : acc p (A ∘ Prod.snd)= G.ad (A p.2.val.1) (A p.2.val.2):=by
  set x:=native (R:=R) (A ∘ Prod.snd) (p.1,p.2.val.1)
  set y:=native (R:=R) (A ∘ Prod.snd) (p.1,p.2.val.2)
  suffices (x*y*x⁻¹*y⁻¹).c=G.ad x.a y.a by unfold acc faceValue; simp only [square, travel,Step.pos_read,Step.neg_read,mul_one,← mul_assoc]; exact this
  rw [conjugate]; simp [c_mul,c_inv,a_inv,ad_same]
end YM.XSpace.Chart2
