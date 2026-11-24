import YM.OPE.Compatible.Swoon.Cull
/-!
# Gaussian cumulant Parser. rips and rank cuts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Coin
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix LinearMap Flock
variable {E F Y I:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
lemma poundA (T:R2 F)(x:F)(A:E→L[ℝ] F)(h:Tensor.Sym T): L.average μ (fun i=> T ![x+A i,x+A i])=T ![x,x]+L.average μ (fun i=> T ![A i,A i]):=by
      let P:E→ℝ:=fun i=>T ![x,x]; let Q:E→ₗ[ℝ] ℝ:=(with2 T x).comp A.toLinearMap; let f(i:E):=T ![A i,A i]; have hp:Bond P:=Bond.keep _; have hQ:Bond Q:=Bond.glyph Q; have hf:Bond f:=by
           change Bond fun i=>T (![A i,A i]); convert Bond.multiline T (fun _ :Fin 2=> (A:E→F)) (fun _ l=> Bond.glyph (l.comp A.toLinearMap)) using 1; funext i; exact congr_arg T (funext fun j=>by fin_cases j<;>rfl)
      change L.average μ _= _+ L.average μ f; rw [show (fun i:E=> T ![x+A i,x+A i])=P+(2:ℝ) • (⇑Q)+f from funext fun i=> buck2 T x (A i) h, sun μ L (hp.add (Bond.scale _ hQ)) hf,sun μ L hp (Bond.scale _ hQ),singleConst,scooted, colorful μ L _ hQ (map_neg Q),mul_zero,add_zero]
def τ0 (T:R3 F)(x:F) := T ![x,x,x]/6
def τ1 (T:R3 F)(x:F)(A:E→L[ℝ] F): E→ₗ[ℝ] ℝ:= (2:ℝ)⁻¹ • {
       toFun i:= T ![A i,x,x]
       map_add' i j:=by rw [map_add]; exact DFunLike.congr_fun (T.curryLeft.map_add (A i) (A j)) ![x,x]
       map_smul' c i:=by rw [map_smul]; exact DFunLike.congr_fun (T.curryLeft.map_smul c (A i)) ![x,x] }
def τ2 (T:R3 F)(x:F)(A:E→L[ℝ] F)(i:E):=T ![x,A i,A i]/2
def τ3 (T:R3 F)(A:E→L[ℝ] F)(i:E):=T ![A i,A i,A i]/6
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ F] in
lemma τEcho (T:R3 F)(h:Tensor.Sym T)(x:F)(A:E→L[ℝ] F): (fun i:E=> T ![x+A i,x+A i,x+A i]/6)= (fun _=> τ0 T x)+⇑(τ1 T x A)+τ2 T x A+τ3 T A:=by
       funext i; rw [buck3 T _ _ h]; change _ = _+(2:ℝ)⁻¹*T ![A i,x,x]+ _ + _; unfold τ0 τ2 τ3; ring
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ F] in
lemma τLow (T:R3 F)(A:E→L[ℝ] F)(x:E): τ3 T A (-x)= -τ3 T A x:=by
       unfold τ3; simp only [map_neg]; let f:=Glass.with3 T; change f (-A x) (-A x) (-A x) /6= -(f _ _ _ /6); simp;ring
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ F] in
lemma τSteep (T:R3 F)(v:F)(A:E→L[ℝ] F)(x:E): τ2 T v A (-x)= τ2 T v A x:=by
       unfold τ2; simp only [map_neg]; let f:=Glass.with3 T; change f v (-A x) (-A x) /2 =f _ _ _ /2; simp
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma τBond (T:R3 F)(p:F)(A:E→L[ℝ] F): Bond (τ2 T p A) ∧ Bond (τ3 T A):=by
     refine ⟨?_,?_⟩
     · unfold τ2; simp_rw [div_eq_mul_inv]; apply Bond.mul (v:=fun _=>(2:ℝ)⁻¹) _ (Bond.keep _); convert Bond.multiline (carg T p) (fun _ :Fin 2=> (A:E→F)) (fun _ c=> Bond.glyph (c.comp A.toLinearMap)) using 1; funext i; change carg T p ![A i,A i]= _; apply congr_arg;ext1 j;fin_cases j<;>rfl
     unfold τ3; simp_rw [div_eq_mul_inv]; apply Bond.mul (v:= fun _=>(6:ℝ)⁻¹) _ (Bond.keep _); convert Bond.multiline T (fun _ :Fin 3=> (A:E→F)) (fun _ c=> Bond.glyph (c.comp A.toLinearMap)) using 1; funext i; apply congr_arg; ext1 j;fin_cases j<;> rfl
lemma τav (T:R3 F)(h:Tensor.Sym T)(x:F)(A:E→L[ℝ] F): L.average μ (fun i:E=> T ![x+A i,x+A i,x+A i]/6) = τ0 T x + L.average μ (τ2 T x A):=by
    rw [τEcho T h]; let c:= τ1 T x A; have ht:= Bond.glyph c; have hh:= Bond.keep (E:=E) (τ0 T x); obtain ⟨hv,hf⟩:= τBond T x A; rw [sun μ L ((hh.add ht).add hv) hf,sun μ L (hh.add ht) hv, sun μ L hh ht,colorful _ _ _ hf (τLow T A),colorful _ _ _ ht (map_neg c),singleConst,add_zero, add_zero]
lemma τipp (T:R3 F)(h:Tensor.Sym T)(p:E)(A:E→L[ℝ] F): L.average μ (⇑(L.P p)*τ3 T A)= L.average μ (τ2 T (A p) A):=by
     apply bask μ L p _ _ (τBond T (A p) A).2 (τBond T (A p) A).1; intro x t
     let a:= A p; let b:= A x; let Q:=T ![a,b,b]; let c:= T ![b,a,a]; let d:=T ![a,a,a]; let y(k:ℝ):= τ0 T b+Q/2*k+c/2*k^2+d/6*k^3
     rw [show (fun r:ℝ=>τ3 T A (x+r • p))=y from ?_]; swap
     · funext r; unfold τ3 y τ0; simp only [map_add,map_smul]; rw [buck3 T _ _ h]; let X:=Glass.with3 T; change (X b b b+3*X (r • a) b b+3 * X b (r • a) (r • a)+X (r • a) (r • a) (r • a))/6= _ -- numeral 6/2 not defeq
       simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; change _ = X b b b /6+X a b b /2*r+ X b a a /2*_+X a a a /6*_;ring
     have ht: HasDerivAt y (0+Q/2*1+c/2*((2:ℝ)*t*1)+d/6*(3*t^2*1)) t:=by
          convert! ((((hasDerivAt_const t (τ0 T b)).add ((hasDerivAt_id' t).const_mul (Q/2))).add (((hasDerivAt_id' t).pow 2).const_mul (c/2))).add (((hasDerivAt_id' t).pow 3).const_mul (d/6))) using 1; norm_num
     convert ht using 1; unfold τ2; simp only [map_add,map_smul,zero_add]; let X:=Glass.with3 T; change X a (b+t • a) (b+t • a)/2= _; simp only [map_add,map_smul,smul_eq_mul]; have h1:X a a b=X b a a:=by let p:= Equiv.swap (0:Fin 3) 2; change T ![a,a,b]=_; rw [show ![a,a,b]=![b,a,a]∘ p from funext fun i=>by fin_cases i<;>rfl]; exact h ..
     rw [LinearMap.add_apply,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,show X a b a=X b a a from pact T a b a h,h1]; change _= X a b b /2* _ + X b a a/2 *_+ X a a a/6*_; simp only [smul_eq_mul];ring
end YM.OPE.Libra.Coin
