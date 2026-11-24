import YM.FVA2.Recall.Frame
import YM.FVA2.Wick.Papers
/-!
 # Real Gaussian moment in g-rescaled directions and its scaling count
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Euler
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E)
local notation "H₀"=> Module.finBasis ℝ E
local notation "I"=> Fin (Module.finrank ℝ E)
local notation "Θ"=> element (E:=E)

/-- Costs evaluated on *one half* of bilinear P. Equivalent to Radial.jet. -/
def double (Q: E →ₗ[ℝ] Module.Dual ℝ E): Permit E:= ∑ i:I, element ((H₀).coord i)*element (Q (H₀ i))
lemma echo (Q: E→ₗ[ℝ] Module.Dual ℝ E)(x:E): (double Q).val x = Q x x:= by
 change ((papers E).val (double Q)) x = _; rw [double,map_sum,Finset.sum_apply]; conv_rhs=> lhs; rhs; rw [←Module.Basis.sum_repr H₀ x]
 simp_rw [map_sum,LinearMap.sum_apply,map_smul]; rfl

def fuel (Q: E→ₗ[ℝ] Module.Dual ℝ E) : Permit E:= (2:ℝ)⁻¹ • double Q
lemma heat (Q:E→ₗ[ℝ] Module.Dual ℝ E)(x:E) : (fuel Q).val x= Q x x / 2:= by unfold fuel; change (2:ℝ)⁻¹ *(double Q).val x=_; rw [echo]; ring
lemma homo_fuel (Q:E→ₗ[ℝ] Module.Dual ℝ E): Paint.Values (fuel Q) 2:= by intro x z; simp_rw [heat,map_smul, LinearMap.smul_apply,smul_eq_mul]; ring

namespace Prices
local notation "H"=> fuel L.P
private lemma differentiates (x:E)(v:Permit E) : (fun y:E=> fderiv ℝ v.val y x) ∈ papers E:= by
 apply Papers.induction (P:=fun v:E→ℝ=> (fun y:E=> fderiv ℝ v y x)∈ papers E) _ _ _ _ v.property
 · intro φ; simp_rw [show ∀ y, fderiv ℝ (⇑φ) y= LinearMap.toContinuousLinearMap φ from (fun y=> ContinuousLinearMap.fderiv (𝕜:=ℝ) (E:=E) («F»:=ℝ) (x:=y) ( LinearMap.toContinuousLinearMap φ ))]; exact Papers.fixed _
 · intro z; change (fun y:E=> fderiv ℝ (fun _ : E=> z) y x)∈papers E; simp_rw [show ∀ y, fderiv ℝ (fun _:E=>z) y=0 from fun i=>(hasFDerivAt_const (𝕜:=ℝ) z i).fderiv]; exact (papers E).zero_mem
 · intro f g hf hg hF hG; simp_rw [ fderiv_add ( (Wick.Boson.Poly.smooth ⟨f,hf⟩).differentiable (by simp) _ ) ( (Wick.Boson.Poly.smooth ⟨g,hg⟩).differentiable (by simp) _ ), _root_.add_apply ]; exact (papers E).add_mem hF hG
 intro f g hf hg hF hG; simp_rw [ fderiv_mul ( (Wick.Boson.Poly.smooth ⟨f,hf⟩).differentiable (by simp) _ ) ((Wick.Boson.Poly.smooth ⟨g,hg⟩).differentiable (by simp) _ ), _root_.add_apply, _root_.smul_apply ]; exact (papers E).add_mem ((papers E).mul_mem hf hG) ((papers E).mul_mem hg hF)

def derive (x:E)(v:Permit E): Permit E:= ⟨_, differentiates x v⟩
lemma slope_t (x:E)(v: Permit E)(y:E)(u:ℝ): HasDerivAt (fun t:ℝ=> v.val (y+t•x)) ((derive x v).val (y+u•x)) u:= ((( Wick.Boson.Poly.smooth v ).differentiable (by simp) _ ).hasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>y+t•x) u (show HasDerivAt (fun t:ℝ=> y+t•x) x u from by simpa using! (HasDerivAt.const_add y ((hasDerivAt_id' u).smul_const x))))
lemma derive_linear (ℓ:Module.Dual ℝ E)(x:E): derive x (element ℓ)=constant (ℓ x):= by
 refine Subtype.ext (funext fun y=>?_); change fderiv ℝ (⇑ℓ.toContinuousLinearMap) y x=_; rw [ ℓ.toContinuousLinearMap.fderiv ];rfl
lemma derive_p (x:E)(p q:Permit E): derive x (p*q)= p* derive x q + q*derive x p:= by
 refine Subtype.ext (funext fun y=>?_); change fderiv ℝ (p.val*q.val) y x=_; rw [ fderiv_mul ((Wick.Boson.Poly.smooth p).differentiable (by simp) _) ((Wick.Boson.Poly.smooth q).differentiable (by simp) _) ]; rfl

private lemma comes_on {v:Permit E}{n:ℕ}(h:Paint.Values v n)(x:E): fderiv ℝ v.val x x=(n:ℝ)*v.val x:= by
 let f(t:ℝ):=(t+1) • x
 have he:f 0=x:=by simp [f]
 have hh:= ( ( Wick.Boson.Poly.smooth v ).differentiable (by simp) x ).hasFDerivAt.comp_hasDerivAt_of_eq 0 (show HasDerivAt f x 0 from by unfold f; simpa using! (((hasDerivAt_id' (0:ℝ)).add_const 1).smul_const x)) he.symm
 change HasDerivAt (fun t:ℝ=> v.val (f t)) _ _ at hh
 simp_rw [show ∀ t:ℝ,v.val (f t)=_ from (fun t=> h x (t+1))] at hh; exact hh.unique (by simpa using! ((((hasDerivAt_id' (0:ℝ)).add_const 1).pow n).mul_const (v.val x)))
lemma total {v:Permit E}{n:ℕ}(h:Paint.Values v n) : ∑ i:I, element ( (H₀).coord i ) * derive ( H₀ i ) v= (n:ℝ) • v:= by
 let f:= H₀
 refine Subtype.ext (funext fun x=> ?_); rw [show (∑ i:I, _ : Permit E).val = _ from _root_.map_sum (papers E).val (fun i=> element ( (H₀).coord i ) * derive ( H₀ i ) v) Finset.univ,Finset.sum_apply]; change (∑ i:I, (f.repr x i) • (fderiv ℝ v.val x (f i))) = (n:ℝ)*v.val x; rw [←comes_on h]; simp_rw [ ← map_smul, ←map_sum, Module.Basis.sum_repr]
variable [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure]
local notation "Ω"=> Papers.opening μ L
lemma priced (x:E)(p:Permit E): Ω (p*element (L.P x))= Ω (derive x p):= by
 let P:= p*element (L.P x); let D:=derive x p; let G:= L.kern; let Δ:= Papers.applies p; have hD:= Papers.applies D
 have he:= L.translation_lemma x Δ.2 Δ.1 hD.2 hD.1 (slope_t x p) μ; rw [sub_mul] at he; change (∫ x:E,( D.val * L.kern ) x - ( P.val * L.kern ) x ∂μ)=0 at he; rw [integral_sub (Papers.useful μ L D) (Papers.useful μ L P)] at he
 exact congr_arg (fun c:ℝ=> c / ∫ x:E,G x ∂μ) (sub_eq_zero.mp he).symm
lemma twoH {p:Permit E}{n:ℕ}(h:Paint.Values p n): 2* Ω (H*p)= (Module.finrank ℝ E+n:ℕ)*Ω p:= by -- notation coerces?
 let F i:= element ( (H₀).coord i )
 calc
    _ = Ω (∑ i:I,(F i * p)*element (L.P (H₀ i))) := by
          rw [show ∑ i:I,(F i * p)*element (L.P (H₀ i))= double L.P * p from ?_]
          · unfold fuel; rw [smul_mul_assoc, map_smul]; change (2:ℝ) * ((2:ℝ)⁻¹ * _)=_; ring
          unfold double; rw [ Finset.sum_mul ]; exact Finset.sum_congr rfl (fun i _=>mul_right_comm .. )
    _ = Ω ( ∑ i:I,( F i * derive (H₀ i) p + p ) ):= by
          rw [map_sum, map_sum]; refine Finset.sum_congr rfl (fun i _=> ?_); rw [priced,derive_p]; unfold F; rw [derive_linear]; simp only [Module.Basis.coord_apply, Module.Basis.repr_self,Finsupp.single_eq_same,constant,map_one,mul_one]
    _ = _:= by rw [Finset.sum_add_distrib,total h,map_add, map_smul]; rw [Finset.sum_const, map_nsmul]; simp; ring
end Prices
end YM.FVA2.Recall.Euler
