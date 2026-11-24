import YM.X.Chir.Rover
/-!
# Exact tensors and unweighted triangle-minus core solitude. Sym Spin contraction of gradients by diagonal Green, includes sign.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
variable {x y:E4}{X Y:Fielding.Walk}
variable (p t v:Tet) (i j:Axis)
-- ψ in Sym(S)
def coat (p t v:Tet)(i j:Axis):ℝ:=∑ x:Axis,∑ y:Axis, mn p i x*mn t x y*mn v j y
lemma coat_q : coat p t v i j= (if p=t then - mn v j i else 0)+∑ k:Tet, η p t k* α_pair (-1) k (-1) v j i := by
    unfold coat; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,mm,add_mul,Finset.sum_add_distrib]; apply congr_arg₂ (· + ·); · by_cases h:p=t<;> simp [h,ite_mul]
    unfold α_pair η_at; change ∑ b:Axis,(∑ k:Tet, _)* mn v j b= _; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; simp only [Finset.mul_sum, mul_assoc];rfl
lemma coat_m : coat p t v i j + coat p t v j i= if i=j then 2*η p t v else 0 := by
    rw [coat_q,coat_q]; simp_rw [α_mm];
    have he : (∑ k:Tet, η p t k* ((if k=v∧i=j then 1 else 0) - η_at k v i j))+ (∑ k:Tet, η p t k*((if k=v∧j=i then 1 else 0)-η_at k v j i)) = 2* (∑ k:Tet, η p t k* (if k=v∧i=j then (1:ℝ) else 0)):= by
       rw [← Finset.sum_add_distrib,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [η_at_flips k v j i]; by_cases h:j=i <;> (first | (rw [h]; ring)| (simp [h,Ne.symm h] <;> ring))
    have hk: (if p=t then -mn v j i else 0)+(if p=t then -mn v i j else 0)=0:= by split_ifs; unfold mn; rw [layout];ring; exact zero_add .. -- mn unfold
    rw [add_add_add_comm,hk,zero_add,he]; by_cases hj:i=j <;> simp [hj]

def ester (n:Side)(e:ℝ)(r:ℝ)(t p v:Tet)(x y w:Site n):ℝ:= ∑ a:Axis,∑ b:Axis,form r t a b* Wpv e (-1) p a n x w * Wpv e (-1) v b n y w
def galley (e:ℝ)(f : Site n→ℝ):ℝ:= e^4*∑ x:Site n,f x
def trinity (n:Side)(e:ℝ)(t p v:Tet)(x y:Site n):= galley e (ester n e (-1) t p v x y)
lemma w_c (x z:Site n)(i:Axis): Wpv e r p i n x z= ∑ a:Axis, form r p a i*((e^3)⁻¹* prong a n x z):= by unfold Wpv; rw [sprite_val,transfer_val, Finset.mul_sum]; apply sum_congr rfl; intro y _; rw [mul_left_comm]
lemma ester_m (n:Side)(e:ℝ)(x y w:Site n): ester n e (-1) t p v x y w= ∑ a:Axis,∑ b:Axis, coat p t v a b * (((e^3)⁻¹*prong a n x w)*((e^3)⁻¹*prong b n y w)):= by
    unfold ester coat; simp_rw [w_c,Finset.mul_sum,Finset.sum_mul]; -- reorder stamp
    let φ(i j a b:Axis):= mn t i j*(mn p a i*( (e^3)⁻¹* prong a n x w))* (mn v b j* ((e^3)⁻¹*prong b n y w))
    change (∑ i:Axis,∑ j:Axis,∑ b:Axis,∑ a:Axis, φ i j a b) = _
    have hh : ∀ i:Axis,(∑ j:Axis,∑ b:Axis,∑ a:Axis, φ i j a b)=∑ a:Axis,∑ b:Axis,∑ j:Axis,φ i j a b:= by
         intro i; rw [Finset.sum_comm]; have hx(j:Axis): (∑ b:Axis,∑ a:Axis,φ i b a j) = ∑ a:Axis,∑ b:Axis,φ i b a j:= Finset.sum_comm; simp_rw [hx]; rw [Finset.sum_comm]
    simp_rw [hh]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold φ; ring
set_option maxHeartbeats 300000 in
lemma valve_t (n:Side)(e:ℝ)(x y:Site n)(he:0<e): trinity n e t p v x y= ∑ a:Axis,∑ b:Axis,coat p t v a b * traceL e x y (prong a) (prong b):= by
    unfold trinity galley traceL; simp_rw [ester_m]; rw [Finset.sum_comm]; rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [sum_comm,Finset.mul_sum]; apply sum_congr rfl; intro j _; rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro b _; field_simp
abbrev haloM (n:Side)(e:ℝ)(t p v:Tet)(x y:Site n):= η p t v * (e⁻¹^2*Interval.green (x-y))
lemma trice (n:Side)(e:ℝ)(x y:Site n)(he:0<e) :
   2*(trinity n e t p v x y-haloM n e t p v x y)= ∑ i:Axis,∑ j:Axis,coat p t v i j*(traceL e x y (prong i) (prong j) - traceL e x y (prong j) (prong i)):= by
    unfold haloM; rw [valve_t p t v n e x y he,← dotTour x y e]; let f(i j:Axis):= traceL e x y (prong i) (prong j); let ψ:=coat p t v; simp_rw [mul_sub, Finset.sum_sub_distrib]; let a:=∑ i:Axis,∑ j:Axis,ψ i j*f i j; let b:=∑ i:Axis,∑ j:Axis,ψ i j*f j i; let l:=η p t v*(∑ i:Axis,f i i); have hh: a+b=2*l:= by
       unfold a b; nth_rw 2 [Finset.sum_comm]; rw [← Finset.sum_add_distrib]; simp_rw [←Finset.sum_add_distrib,←add_mul,ψ,coat_m]; simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]; rw [mul_assoc]; -- no unfold l?
    change 2* a - _ = a - b; change 2*a - 2*l = _; linarith only [hh]
variable (hq:1<q.val)(h:x≠y)(hx:plot q X x)(hy:plot q Y y)
local notation "ε"=> epsilon q
include h hx hy hq
lemma trajectory : Tendsto (fun k=> trinity (side q k) (ε k) t p v (transit q X k) (transit q Y k)) atTop (𝓝 (η p t v * Green (x-y))) := by
    let z (k:ℕ):= haloM (side q k) (ε k) t p v (transit q X k) (transit q Y k); let b:=η p t v*Green (x-y); have he : Tendsto z atTop (𝓝 b):= (sea hq h hx hy).const_mul _; have hz:Clear q 0 X Y:= ⟨x,y,hx,hy,norm_pos_iff.mpr (sub_ne_zero.mpr h)⟩;
    let f(i j:Axis):ℕ→ℝ:= fun k=>coat p t v i j * (Tr q X Y (prong i) (prong j) k-Tr q X Y (prong j) (prong i) k); let g(k:ℕ):=∑ i:Axis,∑ j:Axis,f i j k; have hs:Tendsto g atTop (𝓝 0):= by
       simpa using! tendsto_finsetSum (Finset.univ (α:=Axis)) (fun i _=> tendsto_finsetSum (Finset.univ (α:=Axis)) (fun j _=> show Tendsto (f i j) atTop (𝓝 0) from (by simpa using! (tr_sym hz hq (by norm_num) i j).const_mul (coat p t v i j)))) -- expose g
    have ht : Tendsto (fun k=>g k /2 + z k) atTop (𝓝 b):= by simpa using (hs.div_const (2:ℝ)).add he
    refine ht.congr fun k=> ?_; have hy : 2*(_-z k)=g k:= trice p t v (side q k) (ε k) (transit q X k) (transit q Y k) (epsilon_pos ..); linarith only [hy] -- Tr sym h params inspect
end YM.PositionX.Chir
