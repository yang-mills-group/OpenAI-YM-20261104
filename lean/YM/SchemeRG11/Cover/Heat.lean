import YM.Pert.First.OneArray
import YM.Pert.Warp.Shards
/-! Polynomial Wick symbols on open vertices. No finite-regulator completion claims. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial
variable {R S J I : Type*} [CommRing R] [CommRing S]
abbrev Paper (I R : Type*) [CommRing R] := MvPolynomial I R
abbrev Arrow (I R: Type*) [CommRing R] := Module.End R (Paper I R)
structure Dose (I R : Type*) [CommRing R] where
 pulse : I→I→R
 beats (i j): pulse i j=pulse j i
namespace Dose
variable (D : Dose I R)
def neg : Dose I R := ⟨fun i j=> -D.pulse i j,fun i j=>by rw [D.beats i j]⟩
@[simp] lemma neg_neg : D.neg.neg=D:=by unfold neg; congr; funext i j; exact _root_.neg_neg _
end Dose
open scoped Classical
abbrev vent (z : I→R)  : Derivation R (Paper I R) (Paper I R):= mkDerivation R (fun i=>MvPolynomial.C (z i))
lemma vent_C (z : I→R) (c:R): vent z (MvPolynomial.C c) = 0:= Derivation.map_algebraMap _ _
lemma vent_l (z : I→R) (p q : Paper I R) : vent z (p*q)= p * vent z q + q * vent z p:= (vent z).leibniz ..
lemma vent_x (z : I→R) (p : Paper I R) (i:I) : vent z (p*X i)=(z i) • p + (X i * vent z p):=by rw [vent_l]; simp only [vent,mkDerivation_X,MvPolynomial.smul_eq_C_mul]; rw [mul_comm p]
lemma vents (z w:I→R) (p : Paper I R) : vent z (vent w p)=vent w (vent z p):=by
 induction p using MvPolynomial.induction_on with
 | C c => rw [vent_C,vent_C,map_zero,map_zero]
 | add a b ha hb => rw [map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a j h => simp only [vent_x,map_add]; rw [(vent z).map_smul,(vent w).map_smul,mul_comm (X j) _,mul_comm (X j) (vent z a),vent_x,vent_x,h]; abel
namespace Dose
variable (D : Dose I R)
def polar (i:I) : Arrow I R:= (LinearMap.mul R _ (X i))+(vent (D.pulse i)).toLinearMap
lemma polar_def (i:I) (p : Paper I R): D.polar i p = X i*p + vent (D.pulse i) p:= rfl
lemma pairwise (i j:I): D.polar i*D.polar j=D.polar j*D.polar i:=by
 apply LinearMap.ext; intro p; change polar D i (polar D j p)=polar D j (polar D i p)
 simp only [polar_def,map_add,vent_l,vent, mkDerivation_X]
 rw [D.beats i j,show mkDerivation _ _ (mkDerivation _ _ p) = mkDerivation _ _ (mkDerivation _ _ p) from vents (D.pulse i) (D.pulse j) p]; ring
abbrev nursery:= Algebra.adjoin R (Set.range D.polar)
open scoped IsMulCommutative in
def factory : Paper I R →ₐ[R] Arrow I R:=
 let V : I → D.nursery:= fun i=> ⟨D.polar i,Algebra.subset_adjoin ⟨i,rfl⟩⟩
 haveI := Algebra.isMulCommutative_adjoin R (show ∀ x∈Set.range D.polar,∀ y∈ Set.range D.polar,x*y=y*x by rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩; exact D.pairwise i j)
 D.nursery.val.comp (MvPolynomial.aeval V)
lemma factory_X (i : I) : D.factory (X i)=D.polar i:=by unfold factory; simp

def heat : Paper I R→ₗ[R] Paper I R := LinearMap.flip (M:=Paper I R) D.factory.toLinearMap (1:Paper I R)
lemma heat_def (p : Paper I R): D.heat p=D.factory p 1 := rfl
lemma heat_x (i : I) (p : Paper I R): D.heat (p*X i)=X i * D.heat p + vent (D.pulse i) (D.heat p):=by rw [heat_def,mul_comm,map_mul,factory_X]; rfl
@[simp] lemma heat_one : D.heat 1=1:=by rw [heat_def,map_one D.factory];rfl
@[simp] lemma heat_C (c:R): D.heat (MvPolynomial.C c)=MvPolynomial.C c:=by
 rw [show (MvPolynomial.C c:Paper I R)=c • (1:Paper I R) by rw [MvPolynomial.smul_eq_C_mul,mul_one],map_smul,heat_one]
lemma wind (z:I→R) (p : Paper I R) : vent z (D.heat p) = D.heat (vent z p):=by
 induction p using MvPolynomial.induction_on with
 | C c => rw [heat_C,vent_C,map_zero]
 | add a b ha hb => rw [map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a j h => rw [heat_x,vent_x,map_add,vents z (D.pulse j),mul_comm (X j),vent_x,map_add,map_smul,mul_comm (X j) (vent z a),heat_x,h]; abel
lemma opposite (p : Paper I R): D.neg.heat (D.heat p)=p:=by
 induction p using MvPolynomial.induction_on with
 | C => rw [heat_C,heat_C]
 | add _ _ ha hb => rw [map_add,map_add,ha,hb]
 | mul_X a i h =>
   rw [D.heat_x,map_add,mul_comm (X i), heat_x,← wind, h]
   have he : vent (D.neg.pulse i) = -vent (D.pulse i):= by
     -- ext
     ext v; simp [vent,Dose.neg]
   rw [he, Derivation.neg_apply,mul_comm, add_assoc,neg_add_cancel,add_zero]
@[simp] lemma reverse (p : Paper I R): D.heat (D.neg.heat p)=p:= by simpa only [D.neg_neg] using D.neg.opposite p
lemma wind' (i : I) (p : Paper I R): D.heat (p*X i)=X i * D.heat p + D.heat (vent (D.pulse i) p):=by rw [heat_x,wind]
def avg: Paper I R→ₗ[R] R:= (aeval (R:=R) (fun _:I=>(0:R))).toLinearMap ∘ₗ D.heat
lemma avg_def (p:Paper I R): D.avg p=MvPolynomial.aeval (fun _:I=>(0:R)) (D.heat p):=rfl
@[simp] lemma avg_one : D.avg 1=1:=by rw [avg_def,heat_one,map_one]
@[simp] lemma avg_C (c:R): D.avg (MvPolynomial.C c)=c:=by rw [avg_def,heat_C, aeval_C]; rfl
lemma release (i : I) (p : Paper I R) : D.avg (p*X i)=D.avg (vent (D.pulse i) p):=by rw [avg_def,wind',map_add,map_mul,aeval_X,zero_mul,zero_add];rfl
lemma prune (p:Paper I R) : D.avg (D.neg.heat p)=MvPolynomial.aeval (fun _:I=>(0:R)) p:=by rw [avg_def,D.reverse]
end Dose
end YM.SchemeRG11.Haze
