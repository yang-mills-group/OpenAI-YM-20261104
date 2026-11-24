import YM.QuadraticLocal.Sunrise.Scatter
/-!
# Vertical SUP for all-analytic λ consumers after putting horizontals

Retain unmarked-part normalization, no shortcuts to MS.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Topology Classical ContDiff
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I] (J:Census V)
variable (p:I→ Poly J)
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
local notation "φ"=> I→ℝ
local notation "M"=> MvPolynomial I ℝ
local notation "χω"=> (I→ℝ)×Y
local notation "ξ"=> Poly J
local notation "ν"=> Poly.bead J
open MeasureTheory
variable {f g:(I→ℝ)→ℝ} {T: ((I→ℝ)×Y)→ ℝ}
-- polynomial class and choose.Have separability for Plan.N. & integration.
namespace Bead
variable [MeasurableSpace Y][BorelSpace Y]
variable (L:Law Y) (μ: Measure Y) [μ.IsAddHaarMeasure] (h:Plausible T)
local notation "F"=> Scatter.transmit J p
local notation "A"=> L.average μ
-- choose pure-data finite tensor.Decomposes on ALL marked directions. Useful for Vectored budget and polarization.P.Stencils
structure PureK (T:X×Y→ℝ):Prop where
    pair : ∃ (Z : Type)(_ : Fintype Z)(a:Z→X→ℝ)(b:Z→Y→ℝ), (∀ i,Plausible (a i)) ∧ (∀ i, Plausible (b i)) ∧ ∀ (x:X) (y:Y), T (x,y)=∑ i:Z,a i x*b i y
namespace PureK
variable {P Q: X× Y→ ℝ}
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma art (a:X→ℝ)(b:Y→ℝ)(ha:Plausible a)(hb:Plausible b): PureK (fun z=> a z.1 * b z.2):=⟨⟨PUnit.{1},inferInstance,fun _=>a,fun _=>b,fun _=>ha,fun _=>hb,by simp⟩⟩
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma constant (c:ℝ): PureK (fun (_:X×Y)=>c):=by
 convert art (fun (_:X)=>c) (fun (_:Y)=>1) (Plausible.atom c) (Plausible.atom 1) using 1; ext1 x; simp
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma left (f:X→ℝ)(h:Plausible f): PureK (fun z:X×Y=> f z.1):= by
 convert art f (fun (_:Y)=>1) h (Plausible.atom 1) using 1; ext1 x; simp
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma right (f:Y→ℝ)(h:Plausible f): PureK (fun z:X×Y=> f z.2):= by
 convert art (fun (_:X)=>1) f (Plausible.atom 1) h using 1; ext1 x; simp
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma plus (h:PureK P)(he:PureK Q): PureK (P+Q):=by
 obtain ⟨T,ht,a,b,h,hb,hP⟩ :=h.pair; obtain ⟨W,hw,a',b',hh,hb',hQ⟩:=he.pair
 exact ⟨⟨T⊕W,inferInstance, Sum.elim a a',Sum.elim b b',fun i=>by cases i; exact h _; exact hh _,fun i=>by cases i;exact hb _;exact hb' _,fun x y=>by rw [Pi.add_apply,hP,hQ]; rw [Fintype.sum_sum_type]; rfl⟩⟩ -- type defeq
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma mul (h:PureK P)(he:PureK Q): PureK (P*Q):=by
 obtain ⟨T,ht,a,b,h,hb,hP⟩ :=h.pair; obtain ⟨W,hw,a',b',hh,hb',hQ⟩:=he.pair; refine ⟨⟨T×W,inferInstance,fun i=> a i.1 * a' i.2,fun i=> b i.1 * b' i.2,fun i=>(h _).mul (hh _),fun i=>(hb _).mul (hb' _), fun x y=>?_⟩⟩
 rw [Pi.mul_apply, hP,hQ, Fintype.sum_prod_type, sum_mul]; simp_rw [mul_sum]; apply sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_; change _= (a i x * a' j x)*(b i y * b' j y); ring
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma lin (L:X×Y →ₗ[ℝ] ℝ): PureK (L:X×Y→ℝ):=by
 let a:= L ∘ₗ LinearMap.inl ..; let b:= L ∘ₗ LinearMap.inr ℝ X Y; suffices h:(fun x:X×Y=> L x)= (fun x=> a x.1)+(fun x=> b x.2) by change PureK fun x=> L x; rw [h]; exact (left _ (Plausible.line a)).plus (right _ (Plausible.line b))
 ext1 p; change L p= L (p.1,0)+L (0,p.2); rw [← map_add]; simp
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma orient (h:Plausible P): PureK P:= by induction h with | atom v=> exact constant v | times Q a _ ih=> exact ih.mul (lin a) | add _ _ h h' => exact h.plus h'
end PureK
open Scatter
-- book.Re ∀ i for actual integrable.Pursuant.H.Point.
lemma segregate {J':Type*}(s:Finset J') (a:J'→ℝ){b:J'→Y→ℝ}(h:∀ i∈s,Plausible (b i)): A (fun y:Y=>∑ i ∈ s,a i * b i y)=∑ i∈s,a i * A (b i):=by
 rw [show (fun y:Y=>∑ i∈s,a i*b i y)= (∑ i∈s,a i • b i) from funext fun x=> (Finset.sum_apply x s (fun i=> a i • b i)).symm,
 average_sum L μ (fun i hi=>Plausible.scale (a i) (h i hi))]; simp_rw [average_scale]
lemma ledger (A':PureK T) (W:Poly J →ₗ[ℝ] ℝ) : W (F (fun x: I→ℝ=> A (fun y=> T (x,y)))) = A (fun y=> W (F (fun x:I→ℝ=>T (x,y)))) := by
 obtain ⟨U,hu,a,b,hA,hB,hT⟩:= A'.pair; simp_rw [hT]; let v(i:U):= A (b i)
 have hv(d:U→ℝ) : F (fun x=>∑ i:U,d i * a i x)=∑ i:U,(↑(d i):ℂ) • F (a i):=by
    rw [show (fun x=> ∑ i:U,d i*a i x)=∑ i:U,(d i) • a i from funext fun x=> (Finset.sum_apply x univ (fun i:U=>d i • a i)).symm]; rw [pile _ _ univ (fun i _=> Plausible.scale (d i) (hA _))]; simp_rw [Scatter.mul J p _ (hA _)]
 have hL(d:U→ℝ) : W (F (fun x=>∑ i:U,a i x * d i))=∑ i:U,W (F (a i))*d i:=by
    simp_rw [mul_comm (a _ _)]; rw [hv d, map_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [Complex.coe_smul, map_smul, smul_eq_mul, mul_comm]
 have hM : (fun x:I→ℝ=> A (fun y=>∑ i:U,a i x*b i y))=(fun x=>∑ i:U,a i x*v i):= funext fun i=> segregate L μ Finset.univ (fun y=>a y i) (fun _ _=> hB _)
 rw [hM,hL v]; simp_rw [show ∀ y,W (F (fun x=>∑ i:U, a i x*b i y))= ∑ i:U,W (F (a i))*b i y from fun y=> hL (fun i=> b i y)]; exact (segregate L μ univ (fun i=> W (F (a i))) (fun _ _=> hB _)).symm
-- real/imag projection later.Focus.Reserve.
end Bead
end YM.QuadraticLocal.Sunrise
