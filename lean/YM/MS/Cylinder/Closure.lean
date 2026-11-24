import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Ferry
import YM.MS.Cylinder.Blend
/-! Diagonal rotation sign and jet scaling one. No log rotation yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Filter Set Finset Koszul Taylor
open scoped Topology ContDiff
variable {A B R : Type*}[CommRing R]
lemma sign_letter (i:A)(c:A→R) : graffiti c (single i)= c i • single i:= by
    apply Subtype.ext; funext l; simp only [landc,rent,smul_stack,Pi.smul_apply,smul_eq_mul]; cases l with| nil=> simp [single,atLetter]| cons a l=> cases l with| nil=> by_cases h:i=a <;> simp [single,atLetter,h]| cons b l=> simp [single,atLetter]
lemma off_letter (f : A→R)(u : R) : graffiti f (piece u)= piece u:=Subtype.ext (funext fun l=> by cases l <;> simp [landc,rent,piece,coin])

lemma tagged_scale {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ℝ)(c:A→ℝ)(U:A→E)(h:germ f): rent (fun i=>(c i:ℂ)) (ink U f)=ink (fun i=> c i • U i) f:= by
    funext l; unfold rent; induction l generalizing f with
    | nil=> simp
    | cons i l ih=> rw [D_eval i (ink U f),D_eval i (ink (fun i=> c i • U i) _), inktip,inktip]; rw [show layer (c i • U i) f=c i • layer (U i) f from funext fun x=> map_smul ..,ink_smul _ (germ_layer h _),Pi.smul_apply,← ih (layer (U i) f) (germ_layer h _)]; simp only [List.map_cons,List.prod_cons,smul_eq_mul,mul_assoc]
-- disjoint testing formula for assigning any coordinate
lemma view_cost (c:A→R)(U:B→A→R) (F:Cyl A R): shade U (graffiti c F)=shade (fun i j=>U i j*c j) F:= by
   funext l; induction l generalizing F with
   | nil=>simp [tagged]
   | cons i l ih=>
      obtain ⟨s,hs⟩:=fromCyl F; rw [deriv_lum _ _ _ hs,deriv_lum U _ _ (tagUses _ F hs)]; apply Finset.sum_congr rfl; intro k _; simp only [tagged_s,map_smul, Pi.smul_apply, smul_eq_mul, ih, mul_assoc]
end YM.MS.Cylinder
