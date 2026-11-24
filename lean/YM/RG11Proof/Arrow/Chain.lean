import YM.RG11Proof.Nodes.Forest
import YM.RG11Proof.Scale.Vanish
import YM.RG11Proof.Horizon.Restrict
/-!
# Derivative (or other distinguished-field unary operation) conversion

Translation in separated kernels is an insertion in horizon d+1, not
differentiation of formal coupling. Use common regulator-independent geometry
derivative tests in BOTH prescriptions. This file has enough abstract algebra
to consume that obligation. Does not impose BRST/EOM relations at contact.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Arrow
open PowerSeries YM.RG11.Jets YM.RG11.Nodes YM.RG11.Horizon
open scoped BigOperators Classical

variable {J K R:Type*}{n:ℕ}[Fintype J][Fintype K][CommRing R]

-- x sends input lesser space to upper space where algebras live.

private theorem transmitted {ι:J↪K}{s:Square K R}(h:Held ι s)(i:J)(u:K→R):
   (∑ j:K,u j * s (ι i) j)= ∑ j:J,u (ι j)* (Horizon.take ι s i j):= by
   simp only [Horizon.take_apply]
   classical
   rw [← Finset.sum_map (Finset.univ (α:=J)) ι (fun j=>u j * s (ι i) j)]
   exact (Finset.sum_subset (Finset.subset_univ _) (fun t _ ht=> by rw [h i t (fun ⟨j,hj⟩=>ht (hj ▸ (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩))),mul_zero])).symm


 theorem zeroes {ι:J↪K}(p:Change R K)(hg:Anchored p.g)(hZ: Held ι p.Z){X Y:Rect J K (PowerSeries R)}{a ε b β:reading K (PowerSeries R) (n+1)}
     {N}(hA:∀ i w,Through N (armed (X i) a w) (ε (Fin.cons (ι i) w)))(hB:∀ i w,Through N (armed (Y i) b w) (β (Fin.cons (ι i) w)))
     (hm:∀ w,Through N (plant p.Z (PowerSeries.subst p.g ∘ a) w) (b w))
     (he:∀ w,Through N (plant p.Z (PowerSeries.subst p.g ∘ ε) w) (β w))
     (i:J) (v:Fin n→K):
    Through N (plant p.Z (armed ((Y*p.Z - Horizon.take ι p.Z * subs p.g X) i) (PowerSeries.subst p.g ∘ a)) v) 0:=by
   let S:PowerSeries R→PowerSeries R:=PowerSeries.subst p.g
   let T:PowerSeries R→ₐ[R]PowerSeries R:=substAlgHom (R:=R) hg.permits
   have ht:(T: PowerSeries R→ PowerSeries R)=S:=coe_substAlgHom hg.permits
   let α:=S ∘ a
   let e:=S ∘ ε
   let z:= Horizon.take ι p.Z
   have hf: Through N (plant p.Z (armed ((Y*p.Z) i) α) v) (β (Fin.cons (ι i) v)):=by
       change Through N (plant p.Z (armed (fires p.Z (Y i)) α) v) _
       rw [←porch]; apply Through.trans _ (hB i v); exact through_armed (Y i) hm v
   have hh (x:Fin n→K): Through N (armed ((z * subs p.g X) i) α x) (∑ j:J, z i j * e (Fin.cons (ι j) x)):=by
      unfold armed
      simp_rw [Matrix.mul_apply, subs_apply, Finset.sum_mul]
      rw [Finset.sum_comm]; refine Through.sum ?_; intro j _
      simp only [mul_assoc,← Finset.mul_sum]; apply Through.mul (Through.refl _)
      dsimp only [Function.comp_apply,e,S,α]
      change (T : PowerSeries R→PowerSeries R)=PowerSeries.subst p.g at ht
      simp_rw [←ht]; simp only [← map_mul,←map_sum]
      have hu:= (hA j x).compose (Through.refl p.g) hg
      unfold armed at hu; simp only [←ht] at hu; exact hu
   have hk : Through N (plant p.Z (armed ((z*subs p.g X) i) α) v) (β (Fin.cons (ι i) v)):=by
      apply (through_plant p.Z hh v).trans
      have hu:plant p.Z (fun x=>∑ j:J,z i j*e (Fin.cons (ι j) x)) v=plant p.Z e (Fin.cons (ι i) v):=by
        rw [Plant.germ]; unfold plant
        simp_rw [Finset.sum_mul,Finset.sum_comm (f:=fun (j:K)(w:Fin n→K)=>e (Fin.cons j w)*(p.Z (ι i) j*cross p.Z v w))]
        apply Finset.sum_congr rfl; intro w _
        simp_rw [←mul_assoc,← Finset.sum_mul]; congr 1
        rw [transmitted hZ]
        simp_rw [mul_comm (z i _)]; rfl
      rw [hu]; exact he _
   have hu:= hf.sub hk; rw [sub_self] at hu
   convert! hu using 1; simp only [plant,armed,Matrix.sub_apply,sub_mul, Finset.sum_sub_distrib,α,S]; rfl

-- isolate head with no lower unpaid powers
 theorem invader (D:Square K (PowerSeries R))(hd:nearId D)(a:reading K (PowerSeries R) (n+1)){U:Rect J K (PowerSeries R)}{k}(h:∀i<k,piece i U=0)(i:J)(v: Fin n→K):
      coeff k (plant D (armed (U i) a) v)=armed (piece k U i) (fun w=>constantCoeff (a w)) v:=by
    have hz:coeff k (plant D (armed (U i) a) v)=plant (piece 0 D) (armed (piece k U i) (fun w=>constantCoeff (a w))) v:=by
      unfold plant armed; simp_rw [Finset.sum_mul,map_sum]
      refine Finset.sum_congr rfl (fun w _=>Finset.sum_congr rfl (fun j _=>?_))
      rw [mul_assoc,Scale.hit_coeff _ (p:=U i j) (fun n hn=>congrArg (fun (q:Rect J K R)=>q i j) (h n hn)),map_mul,cross,map_prod,cross]
      simp only [piece_apply,coeff_zero_eq_constantCoeff_apply,mul_assoc]
    rw [hz,hd,plant_id]
end YM.RG11.Arrow
