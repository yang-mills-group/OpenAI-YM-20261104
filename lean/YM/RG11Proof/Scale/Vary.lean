import YM.RG11Proof.Jets.Detector
/-!
# Perturb one layer of all-slot scheme transformation

No trading a formal derivation on coefficients for a derivative on space-time
fields. This is the former ONLY. `varies` over R=ℝ⟦X⟧ can use the epsilon
expansion over that ring via `framePencil` or its erased-slot formula (prove
equivalent). This file isolates product rule & orientation. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.PertExtension.Position YM.RG11.Jets

variable {J R P:Type*}{width:P→ℕ}[Fintype J]
local notation "slots" => PertExtension.Position.insert
section vary
variable [CommRing R]

def varies (a:Mark J width→R) (D U:Square J R) (v:Mark J width):=
    ∑ w:Fin (width v.1)→J,a ⟨v.1,w⟩ * ∑ i,U (v.2 i) (w i) * ∏ k∈Finset.univ.erase i, D (v.2 k) (w k)

variable (a:Mark J width→R)(D U T V:Square J R)

theorem tangent_pencil : varies a D U=framePencil a D U:=by
  funext v
  unfold varies framePencil PertExtension.Position.insert
  rw [map_sum]
  refine Finset.sum_congr rfl (fun w _=>?_)
  rw [coeff_C_mul]; congr 1
  let K (i:Fin (width v.1)):= D (v.2 i) (w i)
  let Y (i:Fin (width v.1)):= U (v.2 i) (w i)
  suffices ∀ (s:Finset (Fin (width v.1))), coeff 1 (∏ i∈s,(C (K i)+ C (Y i)* PowerSeries.X))=∑ i∈s,Y i*∏ k∈s.erase i,K k from (this Finset.univ).symm
  intro s
  induction s using Finset.induction_on with
  | empty=>simp [coeff_one]
  | insert i s hi hs=>
    rw [Finset.prod_insert hi,coeff_one_mul,hs,map_prod,Finset.sum_insert hi, Finset.erase_insert hi, Finset.sum_mul]
    simp only [map_add,map_mul,coeff_C_mul, coeff_X,coeff_C,constantCoeff_C,constantCoeff_X,mul_zero,zero_add,mul_one,add_zero,one_ne_zero,↓reduceIte]
    congr 1
    apply Finset.sum_congr rfl; intro b hb
    have hd : i≠b:= fun he=>hi (he ▸ hb)
    rw [Finset.erase_insert_of_ne hd,Finset.prod_insert (by simp [hi])]; ring

theorem constant_layer (v:Mark J width):
    C (slots J width a (fun i j=>D i j) v) = slots J width (fun v=>C (a v)) (fun i j=>C (D i j)) v:= insert_alg PowerSeries.C a (fun i j=>D i j) v

-- composition orientation
theorem varies_interior (v:Mark J width):
   slots J width (varies a D U) (fun i j=>T i j) v= varies a (T*D) (T*U) v:=by
   let V i j:= C (D i j)+C (U i j)*PowerSeries.X
   let W i j:= C (T i j)
   let L:= slots J width (fun v:Mark J width=>C (a v)) V
   have hw : slots J width (varies a D U) (fun i j=>T i j) v=coeff 1 (slots J width L W v):=by
     rw [tangent_pencil]
     unfold PertExtension.Position.insert
     rw [map_sum]; refine Finset.sum_congr rfl fun w _=> ?_
     rw [show (∏ i,W (v.2 i) (w i)) = _ from Eq.symm (map_prod PowerSeries.C (fun i=> T (v.2 i) (w i)) _),coeff_mul_C]
     rfl
   rw [hw, insert_twice (J:=J) (fun v:Mark J width=>C (a v)) V W, tangent_pencil]
   have he (i j): (∑ k,W i k* V k j)=C ((T*D) i j) + C ((T*U) i j)*PowerSeries.X:=by
     simp_rw [W,V,mul_add, ←mul_assoc,← map_mul,Finset.sum_add_distrib,← Finset.sum_mul,← map_sum,Matrix.mul_apply]
   simp_rw [he]; rfl

theorem varies_exterior (v:Mark J width):
   varies (slots J width a (fun i j=>D i j)) T V v= varies a (T*D) (V*D) v:=by
   let K i j:= C (D i j)
   let W i j:= C (T i j)+C (V i j)*PowerSeries.X
   rw [tangent_pencil,tangent_pencil, framePencil]
   simp_rw [constant_layer]
   change coeff 1 (slots J width (slots J width (fun v=>C (a v)) K) W v)=_
   rw [insert_twice]
   have he (i j): (∑ k,W i k*K k j)=C ((T*D) i j)+C ((V*D) i j)*PowerSeries.X:=by
     have hu(k):W i k*K k j=C (T i k * D k j) + C (V i k * D k j)*PowerSeries.X:=by simp only [K,W,map_mul]; ring
     simp_rw [hu,Finset.sum_add_distrib,←Finset.sum_mul,←map_sum,Matrix.mul_apply]
   simp_rw [he]; rfl

@[simp] theorem varies_orbit (v:Mark J width): varies a 1 U v=orbit a v U:=by rw [tangent_pencil,formula]

def responds (v:Mark J width): Square J R→ₗ[R] R where
  toFun X:=varies a D X v
  map_add':=by intro x y; unfold varies; simp [Matrix.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
  map_smul':=by intro t x; unfold varies; simp only [Matrix.smul_apply, RingHom.id_apply, smul_eq_mul,Finset.mul_sum]; refine Finset.sum_congr rfl (fun w _=>?_); apply Finset.sum_congr rfl; intros; ring

theorem responds_at (v:Mark J width): responds a D v U = varies a D U v :=rfl

def slams (v:Mark J width):(Mark J width→R) →ₗ[R] R where
   toFun a:= slots J width a (fun i j=>D i j) v
   map_add':=by intros; unfold PertExtension.Position.insert; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
   map_smul':=by intros; unfold PertExtension.Position.insert; simp [mul_assoc,← Finset.mul_sum]

theorem slams_at (v:Mark J width): slams D v a=slots J width a (fun i j=>D i j) v:=rfl
end vary
section derivative
variable [CommRing R]

def flash (D:Square J (PowerSeries R)) := D.map (derivative R)
@[simp] theorem flash_at (D:Square J (PowerSeries R))(i j): flash D i j=(derivative R) (D i j):=rfl

theorem derivative_insert (a: ArrayAt J R width)(D:Square J R⟦X⟧)(v:Mark J width):
   derivative R (slots J width a (fun i j=> D i j) v)=slots J width (derivative R ∘ a) (fun i j=>D i j) v+ varies a D (flash D) v:=by
  unfold PertExtension.Position.insert varies
  rw [map_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w _
  let F (i:Fin (width v.1)):=D (v.2 i) (w i)
  let H (i:Fin (width v.1)):=derivative R (F i)
  change derivative R (_*∏ i,F i)= _* _ + a _*∑ i,H i * _
  have he (s:Finset (Fin (width v.1))): derivative R (∏ i∈s,F i)=∑ i∈s,H i * ∏ j∈s.erase i, F j:=by
     induction s using Finset.induction_on with
     | empty=>simp
     | insert b s hb hs=>
       rw [Finset.prod_insert hb,Derivation.leibniz,hs,Finset.sum_insert hb, Finset.erase_insert hb]
       simp only [smul_eq_mul]
       rw [Finset.mul_sum,add_comm,mul_comm (∏ i∈s,F i)]; congr 1
       apply Finset.sum_congr rfl; intro i hi
       have hu:b≠i:=fun h=>hb (h ▸ hi)
       rw [Finset.erase_insert_of_ne hu,Finset.prod_insert (by simp [hb])]; ring
  rw [Derivation.leibniz, he Finset.univ]
  simp only [Function.comp_apply,smul_eq_mul]; rw [add_comm,mul_comm (∏ i,F i)]
end derivative
end YM.RG11.Scale
