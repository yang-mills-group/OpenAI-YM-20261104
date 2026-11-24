import YM.RG11Proof.Nodes.Question
import YM.RG11Proof.Scale.Vanish
/-!
# Portable Ward tests on leading stress

Stipulate independently specified normalized continuum prescriptions each
obey THROUGH N linear Mandate(s) with same signs/order/sym on separated
reporting arrays. Such premise is not a declaration of equality of stress
on measurement frames. Use joint shape conversion with all slots to derive
normalization laws. No off-shell spin or BV conclusion implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Stress
open scoped Classical BigOperators
open PowerSeries YM.RG11.Jets YM.RG11.Nodes
variable {R I J P : Type*} {n:ℕ}[CommRing R][Fintype I][Fintype J]

-- I indexes components of stress (axis×axis), e.g. divergence tests take
-- shell for translation in ONE direction in stress slots.

abbrev facets (I J R:Type*) (n:ℕ):= I → reading J (PowerSeries R) (n+1)

def relays (X:Rect I J (PowerSeries R))(A:facets I J R n)(v:Fin n→J):PowerSeries R:= ∑ a:I, armed (X a) (A a) v

-- each mandate applied for all values of the other slots
structure Mandate (X:Rect I J (PowerSeries R))(A:facets I J R n)(B:reading J (PowerSeries R) n)(N:ℕ):Prop where
   reach (v:Fin n→J):Through N (relays X A v) (B v)

theorem mandate_forces {d:Change R J}(hg: Anchored d.g){a b:facets I J R n}{P Q:reading J (PowerSeries R) n}{N}
    (h:∀ i v,Through N (plant d.Z (fun w=>PowerSeries.subst d.g (a i w)) v) (b i v))
    (h':∀ v,Through N (plant d.Z (fun w=>PowerSeries.subst d.g (P w)) v) (Q v))
    {X Y:Rect I J (PowerSeries R)}(hX:Mandate X a P N)(hY:Mandate Y b Q N)(v:Fin n→J):
       Through N (plant d.Z (relays (Y*d.Z-subs d.g X) (fun i w=>PowerSeries.subst d.g (a i w))) v) 0:=by
    let t:PowerSeries R→ₐ[R] PowerSeries R:=substAlgHom (R:=R) hg.permits
    have ht (u:PowerSeries R): PowerSeries.subst d.g u = t u :=(congrFun (coe_substAlgHom hg.permits) u).symm
    let U(i:I)(w:Fin (n+1)→J):=PowerSeries.subst d.g (a i w)
    have he(w:Fin n→J): relays (subs d.g X) U w=PowerSeries.subst d.g (relays X a w):=by
       simp_rw [relays,armed,U,subs_apply,ht,map_sum,map_mul]
    have H (w:Fin n→J) := (hX.reach w).compose (Through.refl d.g) hg
    have hXY: Through N (plant d.Z (relays (subs d.g X) U) v) (Q v):=
      (through_plant d.Z (fun i=> by rw [he i]; exact H i) v).trans (h' v)
    have hW : Through N (plant d.Z (relays (Y*d.Z) U) v) (Q v):=by
       unfold relays; rw [planting_total]; apply Through.trans _ (hY.reach v)
       refine Through.sum (fun i _=> ?_)
       change Through N (plant d.Z (armed (fires d.Z (Y i)) (U i)) v) _
       rw [← porch]; exact through_armed (Y i) (h i) v
    have hQ:= hW.sub hXY
    rw [sub_self] at hQ
    convert! hQ using 1
    simp only [relays,Matrix.sub_apply,armed,plant,Finset.sum_mul,sub_mul,Finset.sum_sub_distrib,U]

-- First unpaid residual curbs all other operands at their leading costs.
theorem curb (D: Square J (PowerSeries R)) {U:Rect I J (PowerSeries R)}(a:facets I J R n){k}(h:∀ i<k,piece i U=0)(v:Fin n→J)
     (hD:nearId D):
     coeff k (plant D (relays U a) v) = ∑ i:I,armed (piece k U i) (fun w:Fin (n+1)→J=>constantCoeff (a i w)) v:=by
   let X(i:I):=fun w:Fin (n+1)→J=>constantCoeff (a i w)
   have H : coeff k (plant D (relays U a) v) = plant (piece 0 D) (fun v=>∑ i,armed (piece k U i) (X i) v) v:=by
     unfold plant relays armed
     simp_rw [Finset.sum_mul, map_sum]
     refine Finset.sum_congr rfl (fun w _=> Finset.sum_congr rfl (fun z _=> Finset.sum_congr rfl (fun i _=>?_)))
     rw [mul_assoc,Scale.hit_coeff k (p:=U z i) (fun n hn=>congrArg (fun (q:Rect I J R)=>q z i) (h n hn)),map_mul,cross,map_prod,cross]
     simp only [X,mul_assoc,piece_apply,coeff_zero_eq_constantCoeff_apply]
   rw [H,hD,plant_id]
end YM.RG11.Stress
