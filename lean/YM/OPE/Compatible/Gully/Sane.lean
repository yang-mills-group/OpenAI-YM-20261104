import YM.OPE.Compatible.Gully.Duo
/-!
# Finite period. Born cubic certificate
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Nestle Balsam Weir
open GaussianScore Libra WithLp
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
abbrev Stray (G:Gauge)(n:Side):= Axis→Site n→G.Color
lemma Wj_sum (a b: Stubble.Tile G): Wj (a+b)=Wj a+Wj b:=by simp only [Wj,Pi.add_apply]; abel
lemma Wj_sml (a:Stubble.Tile G)(b:ℝ): Wj (b • a)=b • Wj a:=by simp only [Wj,Pi.smul_apply,smul_add,smul_sub]
lemma lay_s (p:Face (Per n))(a b:Stray G n): layoutA (a+b) p=layoutA a p+ layoutA b p:=by funext i;fin_cases i<;>rfl
lemma lay_m (p:Face (Per n))(a:Stray G n)(t:ℝ):layoutA (t • a) p=t • layoutA a p:=by funext i;fin_cases i<;>rfl
lemma raze (F Y Z:Stray G n)(t:ℝ) :scribeX (t • F) Y Z=t*scribeX F Y Z∧scribeX F (t • Y) Z=t*scribeX F Y Z∧scribeX F Y (t • Z)=t*scribeX F Y Z:=by
   unfold scribeX hatB; simp_rw [lay_m,Wj_sml,map_smul (Al G),LinearMap.smul_apply]; -- Ambig
   simp_rw [map_smul, real_inner_smul_left, real_inner_smul_right,← Finset.mul_sum];simp
lemma syme (F Y Z:Stray G n): scribeX F Y Z=scribeX F Z Y:=by unfold scribeX hatB; apply Finset.sum_congr rfl; intro i _;rw [al_rot _ (layoutA Z i)]
lemma med (F F' Y Z:Stray G n):scribeX (F+F') Y Z=scribeX F Y Z+scribeX F' Y Z ∧scribeX Y (F+F') Z=scribeX Y F Z+scribeX Y F' Z:=by
   unfold scribeX hatB; simp_rw [lay_s,Wj_sum,map_add (Al G),LinearMap.add_apply];simp_rw [map_add,inner_add_left,inner_add_right,Finset.sum_add_distrib];simp
abbrev sal (G:Gauge)(n:Side): Stray G n →ₗ[ℝ] Stray G n →ₗ[ℝ]Stray G n →ₗ[ℝ]ℝ where
   toFun x:= {
      toFun y:={toFun z:=scribeX x y z, map_add':=fun a b=>Eq.trans (syme ..) ((med a b x y).2.trans (congrArg₂ (·+·) (syme ..) (syme ..))), map_smul':=fun t v=> (raze x y v t).2.2}
      map_add' a b:= LinearMap.ext fun p=>(med a b x p).2
      map_smul' a b:= LinearMap.ext fun p=>(raze x b p a).2.1}
   map_add' a b:=LinearMap.ext fun p=> LinearMap.ext fun y=> (med a b p y).1
   map_smul' a b:=LinearMap.ext fun p=>LinearMap.ext fun y=>(raze b p y a).1
lemma stare {E F W: Type} [Fintype E][Fintype F][Fintype W](f:E→Stray G n)(g:F→Stray G n)(y:W→Stray G n): scribeX (∑ i,f i) (∑ i,g i) (∑ i,y i)=∑ i,∑ j,∑ k,scribeX (f i) (g j) (y k):=by
   change sal G n (∑ i, f i) _ _=_; simp_rw [map_sum (sal G n),LinearMap.sum_apply,map_sum,LinearMap.sum_apply]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_comm (f:=fun v w=>(((sal G n) (f i)) (g w)) (y v)))
variable {U:Gloam}
def Ghost (p:Pose)(H:Even n.val)(b:Site n)(x:G.ColorIndex)(A:Law (Keys G (Limb H))):= exclaim H (A.inverse (poseT H b x p))
lemma ghostP (H:∀ i,Even (U.M i).val)(c:Crew U)(p:Pose)(x:G.ColorIndex)(i:ℕ)(h:4≤r):
     Ghost p (H i) (c.val i) x (boost (H i) (Train.top r) h C) =∑ j:Kv, skid (fun a k=> vote (reed p j) ⟨fun i=>decks j (c.val i),orbitB0 U c j H⟩ a i k) (torque p j • expo x):=by
    funext a v; unfold Ghost; rw [ear_spec]; simp_rw [Finset.sum_apply,Finset.sum_smul]; refine Finset.sum_congr rfl (fun k _=>?_); unfold skid; erw [smul_smul,mul_comm (torque p k)];rfl
lemma ledge_Fruit (H:∀ i,Even (U.M i).val)(a b c:Crew U)(p q t:Pose)(x y z:G.ColorIndex)(h:4≤r):
 let L(i):=boost (H i) (G:=G) (Train.top r) h C
 Fruit U (Nestle.win p q t) (fun i=> scribeX (Ghost p (H i) (a.val i) x (L i)) (Ghost q (H i) (b.val i) y (L i)) (Ghost t (H i) (c.val i) z (L i))) 0:=by -- unused f
   intro L
   let R (p:Pose)(a:Crew U)(x:G.ColorIndex)(w:Kv)(i:ℕ):Stray G (U.M i):= skid (fun b k=> vote (reed p w) ⟨fun i=>decks w (a.val i),orbitB0 U a w H⟩ b i k) (torque p w • expo x)
   let D(j k l: Kv)(i:ℕ):=scribeX (R p a x j i) (R q b y k i) (R t c z l i)
   have he(j k l:Kv): Fruit U (Nestle.win p q t) (D j k l) 0:=by
      let F (x:Crew U)(j:Kv):Crew U:=⟨fun i=>decks j (x.val i),orbitB0 U x j H⟩
      let N:=harp (torque p j • expo x) (torque q k • expo y) (torque t l • expo z); rw [show D j k l= Nestle.hash (vote (reed p j) (F a j)) (vote (reed q k) (F b k)) (vote (reed t l) (F c l)) N from funext fun i=> ?_ ]; exact comic (Eventually.of_forall H) _ _ _ (reed p j) (reed q k) (reed t l) (bol (torque p j • expo x) (torque q k • expo y) (torque t l • expo z)); exact largo (vote (reed p j) (F a j)) (vote (reed q k) (F b k)) (vote (reed t l) (F c l)) _ _ _ i
   have hV(j k): Fruit U (Nestle.win p q t) (∑ l,D j k l) 0:=by have hh:=Fruit.line Finset.univ (D j k) (fun _=>0) (fun l _=>he j k l); simpa only [Finset.sum_const_zero] using! hh -- finset e
   have hx(j): Fruit U (Nestle.win p q t) (∑ k,∑ l,D j k l) 0:=by simpa only [Finset.sum_const_zero] using! (Fruit.line Finset.univ (fun k=>∑ l,D j k l) (fun _=>0) (fun k _=>hV j k))
   convert! (show Fruit U (Nestle.win p q t) (∑ j,∑ k,∑ l,D j k l) 0 from by simpa only [Finset.sum_const_zero] using! (Fruit.line Finset.univ _ _ (fun j _=>hx j))) using 2 with i
   unfold L; rw [ghostP H a p x i h (C:=C), ghostP H b q y i h (C:=C), ghostP H c t z i h (C:=C), stare];simp_rw [Finset.sum_apply];rfl
end YM.OPE.StageLight
