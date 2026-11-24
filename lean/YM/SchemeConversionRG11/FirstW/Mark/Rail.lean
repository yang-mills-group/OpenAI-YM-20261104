import YM.SchemeConversionRG11.FirstW.Mark.Riverbed
/-! Degree two logarithmic/path coefficients, including linear varying local gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Lattice Pert Pert.Align Topology Maxwell
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {X : Type*} [AddCommGroup X] [One X] {G : Gauge}
def boardAt (x : Four X) (d : Step) : Wind G X →ₗ[ℝ] G.Color := (if d.neg then -1 else (1:ℝ)) • LinearMap.proj (d.used x)
def rail (x : Four X) : Walk → Wind G X →ₗ[ℝ] G.Color
  | []=>0
  | i::t=>boardAt x i+rail (x+i.vec) t
def swerve (x : Four X) : Walk → Wind G X →ₗ[ℝ] Wind G X→ₗ[ℝ] G.Color
  | []=>0
  | d::t=> (G.ad.compl₂ (rail (x+d.vec) t) ∘ₗ boardAt x d)+swerve (x+d.vec) t
lemma swerve_eq (x : Four X) (d : Step) (t : Walk) (A B : Wind G X) : swerve x (d::t) A B=G.ad (boardAt x d A) (rail (x+d.vec) t B)+ swerve (x+d.vec) t A B := rfl
lemma ad_for (u v : G.Color) : G.ad u v= -G.ad v u := by
  apply G.colorMat_injective -- name?
  rw [G.colorMat_ad,G.colorMat.map_neg,G.colorMat_ad]; abel
lemma ad_diag0 (u : G.Color) : G.ad u u=0 := by apply G.colorMat_injective; rw [G.colorMat_ad,sub_self,map_zero]

def shiftT (e : Four X → G.Color) : Wind G X →ₗ[ℝ] Wind G X := LinearMap.pi fun l=> ((1/2:ℝ) • G.ad (e l.1+e (l.1+step l.2))) ∘ₗ LinearMap.proj l
lemma leg_shiftT (e : Four X→G.Color) (x : Four X) (d : Step) (A : Wind G X) :
    (2:ℝ) • boardAt x d (shiftT e A)=G.ad (e x+e (x+d.vec)) (boardAt x d A) := by
  rcases d with ⟨j,h|h⟩ <;> simp only [boardAt,Step.vec, Step.used, shiftT,LinearMap.smul_apply, LinearMap.proj_apply,LinearMap.pi_apply, LinearMap.comp_apply]
  · simp [smul_smul]
  simp only [↓reduceIte,neg_smul,one_smul,←sub_eq_add_neg,map_neg,smul_smul,sub_add_cancel]
  rw [add_comm (e x)]; norm_num; rw [add_comm]
lemma leg_moment (e : Four X→G.Color) (x : Four X) (d : Step) : boardAt x d (momentE e)=e x-e (x+d.vec) := by
  rcases d with ⟨j,h|h⟩ <;> simp [boardAt,momentE,Step.vec,Step.used,sub_eq_add_neg,add_comm]
lemma reads_mom (e : Four X→G.Color) (x : Four X) (w : Walk) : rail x w (momentE e) = e x-e (stop x w) := by
  induction w generalizing x with | nil=> simp [stop,rail] | cons i w ih=>simp [stop,rail, ih,leg_moment]
lemma turn_inter (e : Four X→G.Color) (x : Four X) (w : Walk) (A : Wind G X) :
    swerve x w A (momentE e)+swerve x w (momentE e) A +(2:ℝ) • rail x w (shiftT e A) = G.ad (e x+e (stop x w)) (rail x w A) := by
  induction w generalizing x with
  | nil=>simp [rail,swerve]
  | cons i w ih=>
    let P:=momentE e; let s:=x+i.vec; let b:=stop s w
    let a:=boardAt x i A; let r:=rail s w A
    rw [swerve_eq,swerve_eq,leg_moment, reads_mom, rail,LinearMap.add_apply, LinearMap.add_apply,smul_add,leg_shiftT]
    change G.ad a (e s-e b)+swerve s w A P+(G.ad (e x-e s) r+ swerve s w P A)+(G.ad (e x+e s) a+ (2:ℝ) • rail s w (shiftT e A))=_
    calc _ = G.ad a (e s-e b) + G.ad (e x-e s) r+ G.ad (e x+e s) a + (swerve s w A P+swerve s w P A+(2:ℝ) • rail s w (shiftT e A)) := by abel
         _ = _ := by rw [ih s]; change _+G.ad (e s+e b) r = G.ad (e x+e b) (a+r); rw [ad_for a]; simp only [map_sub,map_add, LinearMap.sub_apply,LinearMap.add_apply]; abel
open Pert.First
def pointU (A : Wind G X) (r : ℝ) : Links X G.El := fun l => G.lieExp (r • A l)
lemma rail_tried (A : Wind G X) (w : Walk) (x : Four X) : Tried (fun r=>G.mat (travel (pointU A r) x w)) (rail x w A) (swerve x w A A) := by
  induction w generalizing x with
  | nil=>
    convert! glow_tried (v:=(0:G.Color)) using 1; ext t; simp [glow,travel]
  | cons d w ih=>
    have he := glow_tried (v:=boardAt x d A)
    have eq : glow (boardAt x d A) = fun r=>G.mat (d.read (pointU A r) x) := by
      funext r
      unfold Step.read; split_ifs with h
      · rw [show boardAt x d A=- A (d.used x) by simp [boardAt,h]]; exact Eq.symm (glow_inv ..)
      rw [show boardAt x d A= A (d.used x) by simp [boardAt,h]]; rfl
    simp_rw [travel,G.mat_mul]; rw [eq] at he; rw [swerve_eq, add_comm (G.ad _ _),←zero_add (swerve (x+d.vec) w A A)] -- last placeholder
    exact he.product (ih _)
def patch (w : Walk) (i j : Axis) := w++square i j++Lattice.reverse w
lemma trace_ride (w : Walk) (x : Four X) (i j : Axis) (U : Links X G.El):
    G.curvature (travel U x (patch w i j))= Bare.plateU U x w i j := by
  simp only [patch,Bare.plateU,travel_append, stop_append,square_stop, travel_reverse, G.curvature_conjugate]
lemma echo_once (x : Four X) (A : Wind G X) (s : Walk) (i j) : iteratedDeriv 1 (fun r=>Bare.plateU (pointU A r) x s i j) 0 = rail x (patch s i j) A := by
  simp_rw [← trace_ride]
  obtain ⟨z,hz,he,_hh⟩ := (rail_tried A (patch s i j) x).slope_eq
  rw [iteratedDeriv_one]
  exact (Work.F03.curvature_of_hasDerivAt (hz ▸ he 0)).deriv
lemma echo_exact (x : Four X) (A : Wind G X) (s : Walk) (i j) : iteratedDeriv 2 (fun r=>Bare.plateU (pointU A r) x s i j) 0 = swerve x (patch s i j) A A := by
  simp_rw [← trace_ride,recover_group]; exact Tried.decode_second (rail_tried A _ _)
-- equal native path leading stencil is untransported curl after route cancellation
lemma rail_plus (A : Wind G X) (x : Four X) (a b : Walk) : rail x (a++b) A=rail x a A +rail (stop x a) b A := by
  induction a generalizing x with | nil=> simp [rail,stop] | cons i a ih=> rw [List.cons_append,rail, LinearMap.add_apply,ih,rail, LinearMap.add_apply,add_assoc]; rfl
lemma rail_reverse (A : Wind G X) (x : Four X) (a : Walk) : rail (stop x a) (Lattice.reverse a) A= -rail x a A := by
  induction a generalizing x with
  | nil=> simp [rail,stop, Lattice.reverse]
  | cons i a ih=>
    have eh : boardAt (x+i.vec) i.rev A= -boardAt x i A := by cases i with | mk d n=> cases n <;> simp [boardAt,Step.rev, Step.used,Step.vec,sub_eq_add_neg]
    rw [show Lattice.reverse (i::a)=Lattice.reverse a ++ [i.rev] by simp [Lattice.reverse],rail_plus]; simp only [stop]; rw [reverse_stop,ih]; change - _ + (boardAt _ _ A+0) = -(_ + _)
    rw [eh,add_zero]; abel
lemma frontRail (A : Wind G X) (x : Four X) (i j : Axis) : rail x (square i j) A = Bare.wideCurl A x i j := by
  have e (f : Axis) (y:Four X) : boardAt y (negDir f) A = -A (y-step f,f) := by simp [boardAt, negDir,Step.used]
  have h (f : Axis) (y:Four X) : boardAt y (posDir f) A = A (y,f) := by simp [boardAt, posDir, Step.used]
  simp only [square,rail, LinearMap.add_apply, h,e,Bare.wideCurl,add_zero,Step.vec_pos,Step.vec_neg, ←sub_eq_add_neg]
  rw [show x+step i+step j-step i=x+step j by abel, add_sub_cancel_right]; abel
lemma patched (A : Wind G X) (x : Four X) (w : Walk) (i j : Axis) : rail x (patch w i j) A = Bare.wideCurl A (stop x w) i j := by
  simp only [patch,rail_plus,stop_append,square_stop,rail_reverse, frontRail]; abel
end YM.RG11.FirstW
