import YM.OPE.Compatible.Speke.Yew
/-!
# Multiplicative gains are applied to already repaired arrays
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
open Pose (epic)
variable {U:Gloam}{d r:ℝ}{K:ℕ→ℕ}{k j l m:ℕ}{X Y Z:Panels}{A:Zem}{x y:Axis}
lemma payScalar (c:ℝ){a:ℕ→ℝ}{x:ℝ}(hp:Fruit U k a x):Fruit U k (fun i=>c*a i) (c*x):=by
    convert! hp.pen (g:=fun _=>c) (j:=0) (y:=c) (show Bloom U 0 _ _ from ⟨sake_one ..,by simp only[pow_zero,inv_one,one_mul]; exact Cleared.always,by simp⟩) using 1; · funext i;  change c*a i=a i*c;ring
    ring
lemma cubFlip (X Y Z:Panels)(A:Zem)(K:ℕ→ℕ):Triad K A X Y Z=Triad K A.flip X Z Y:=rfl -- def
abbrev TimeA (K:ℕ→ℕ)(X Y Z:Panels)(x y:Axis)(p:Fin 4×Fin 4)(i:ℕ):=∑ z∈pod (K i), dart X x y i z*plume Y x y p.1 i z *plume Z x y p.2 i z
abbrev chi (A:Zem)(p:Fin 4×Fin 4):ℝ:= A (Pi.single p.1 1) (Pi.single p.2 1)
lemma chil (A:Zem)(X Y:Tile): A X Y=∑ p:Fin 4×Fin 4,chi A p*X p.1 * Y p.2:=by
   have hx (X:Tile): ∑ i:Fin 4,X i • Pi.single i (1:ℝ)=X:=by ext k; simp [Pi.single_apply]
   nth_rw 1 [←hx X,←hx Y]; rw [map_sum (A),Fintype.sum_prod_type, LinearMap.sum_apply]; refine Finset.sum_congr rfl (fun i hi=> ?_); rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul, map_smul (A), LinearMap.smul_apply]; change Y j*(X i*_)= _*X i*Y j; unfold chi; ring
lemma hotSeries {f: Fin 4×Fin 4→ℝ}(hp:∀ p,Fruit U k (TimeA K X Y Z x y p) (f p)): Fruit U k (cubic K A X Y Z x y) (∑ p, chi A p*f p):=by
    rw [show cubic K A X Y Z x y=∑ p:Fin 4×Fin 4, fun i=>chi A p* TimeA K X Y Z x y p i from ?_]; exact (Fruit.line _ _ _ (fun p _=> payScalar _ (hp _))) -- indices
    funext i; unfold cubic; rw [Finset.sum_apply]; unfold TimeA; simp_rw [fun z=> chil A (yard (fun a=> Y a i) z x y) (yard (fun a=>Z a i) z x y),Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun p _=>Finset.sum_congr rfl fun z _=>?_); unfold plume dart; ring
lemma hotNone (hp:∀ p,Fruit U k (TimeA K X Y Z x y p) 0): Fruit U k (cubic K A X Y Z x y) 0:=by have ht:= hotSeries (A:=A) hp; simpa using ht
lemma receipt {f:Axis→Axis→ℝ}(hp:∀ x y,Fruit U k (cubic K A X Y Z x y) (f x y)):Fruit U k (Triad K A X Y Z) (Pose.half_sum f):=Fruit.line _ _ _ (fun _ _=>hp _ _)
lemma receiptV (hp:∀ x y,Fruit U k (cubic K A X Y Z x y) 0):Fruit U k (Triad K A X Y Z) 0:=by have h:=receipt (f:=fun _ _=>0) hp; simpa only[Pose.half_sum,Finset.sum_const_zero] using h
end YM.OPE.Nestle
