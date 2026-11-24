import YM.MSbar.Lodge.Throat
import YM.MSbar.Alto.Suez
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι τ:Type}[Fintype σ][Fintype τ][Fintype ι][DecidableEq ι][DecidableEq σ][DecidableEq τ]
variable {m p:ℕ}
local notation "µ"=> PowerSeries.coeff
local notation "P"=> Pot σ
local notation "Q"=> Pot ι
local notation "V"=> View σ
local notation "W"=>View ι
abbrev SpringK (σ:Type):= PowerSeries (Pot σ)
local notation "R"=> SpringK σ
-- concrete directional polynomial partial
noncomputable def dint (b:View σ) : Module.End ℝ (Pot σ):= ∑ i:σ, b i • (pderiv i).toLinearMap
variable (b:View σ)(k: Matrix σ σ ℝ)(f:Pot σ)(x: View σ)
lemma dintX (i:σ): dint (bolt i:View σ) f = pderiv i f:=by unfold dint; simp [bolt,Pi.single_apply,ite_smul]
lemma dimY : fderiv ℝ (fun z=> MvPolynomial.eval z f) x b= eval x (dint b f):=by
    nth_rw 1 [Lis.spiral b]; unfold dint; simp_rw [LinearMap.sum_apply,_root_.map_sum,LinearMap.smul_apply]; refine sum_congr rfl (fun i _=>?_); rw [_root_.map_smul,← C_mul', _root_.map_mul,eval_C]; change b i * fderiv ℝ _ _ _= _; congr 1; have hh: bolt i= Pi.single (M:=fun _ : σ=>ℝ) i 1:=by ext p;simp [bolt,Pi.single_apply];
    rw [hh]; exact (congr_fun (Bakery.TonD i f) x)
lemma dimK (A:Matrix σ ι ℝ)(b:View ι): dint b (rail A f)=rail A (dint (A *ᵥ b) f):=by
    apply MvPolynomial.funext; intro x; rw [← dimY]; have hf: (fun i:View ι=> eval i (rail A f))=fun i => eval (A *ᵥ i) f := funext (fun i=> congr_fun (clearL A i) f); let L:= (toLin' A).toContinuousLinearMap; rw [hf]; change fderiv ℝ ((fun k:V=>eval k f) ∘ L) x b=_; rw [ fderiv_comp _ ((vent f).contDiffAt.differentiableAt (by simp)) L.differentiableAt, L.fderiv]; refine (dimY _ _ _).trans ?_; exact (congr_fun (clearL A x) _).symm
lemma desS (k:Matrix σ σ ℝ): bowl k (dint b f)=dint b (bowl k f):=by
    let q : Module.End ℝ P:=stove k; let u : Module.End ℝ P:=dint b; have he(j:σ)(n:ℕ): (q^n) (pderiv j f)=pderiv j ((q^n) f):=by induction n with|zero=> rfl|succ i ih=> rw [pow_succ']; change _=_; refine (congr_arg q ih).trans (lever k _ _)
    have hv(n:ℕ):pour k (dint b f) n = u (pour k f n):=by unfold pour; rw [_root_.map_smul]; congr 1; unfold u dint; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,_root_.map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; exact congr_arg _ (he i n)
    have hs : pearl k (u f) = elevatorP u (pearl k f):=by apply Polynomial.ext; intro n; rw [season, show (elevatorP u _).coeff n= _ from riseP u (pearl k f) n, season]; exact hv n
    unfold bowl; rw [show pearl k (dint b f)=_ from hs,slipE _ _] -- fragile
lemma dime (x y:View σ): dint (x+y) f=dint x f+dint y f:=by unfold dint; simp only [Pi.add_apply, add_smul, sum_add_distrib]; rfl
open MeasureTheory
variable (C:Matrix σ τ ℝ) {D:Matrix τ τ ℝ} (h:D.PosDef)(A:Matrix σ ι ℝ)
local notation "L"=> C*D*C.transpose
local notation "δ"=>fieldLaw D
local notation "B"=> View τ
variable (u : View τ)
local notation "S"=> fun y:View τ=> x+C *ᵥy
include h
-- score constant α at V, equals gaussian affine. δ covariance.Deck.
lemma incomes (F':ℝ)(Z':Pot σ)(he:∀ y:View τ,eval (x+C*ᵥy) Z'= F'+ dotProduct (D⁻¹*ᵥy) u) :
    eval x (bowl L (Z'*f))= F'*eval x (bowl L f) + eval x (bowl L (dint (C *ᵥ u) f)):=by
    let g(y:B):= eval (S y) f; let v':= dint (C*ᵥu) f; let q(v:B):=eval (S v) v'; have hz(w:P): Integrable (fun y=> eval (S y) w) δ:= (grille C h w x 1 (by norm_num)).integrable le_rfl
    have hx(w:P): eval x (bowl L w)=∫ y,eval (S y) w∂δ:= show Summer D C x w from seen C x h w
    have hu(y:B):dotProduct (D⁻¹*ᵥy) u* g y= eval (S y) (Z'*f)-F'*g y:=by rw [_root_.map_mul,he]; unfold g; ring
    have hc: Continuous S:=continuous_const.add (toLin' C).continuous_of_finiteDimensional
    have hp: Integrable (fun y=> dotProduct (D⁻¹*ᵥy) u*g y) δ:=by simp_rw [hu]; exact (hz _).sub ((hz _).const_mul _)
    have he'(y:B): HasDerivAt (fun t:ℝ=> g (y+t•u)) (q y) 0:=by
        unfold g; simp_rw [Matrix.mulVec_add,mulVec_smul, ← add_assoc]; have ht:HasDerivAt (fun t:ℝ=> S y+t • (C*ᵥu)) (C*ᵥu) 0:= by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const (C*ᵥu)).const_add (S y)
        have hh := ((vent f).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (0:ℝ) ht; rw [zero_smul, add_zero, dimY] at hh; exact hh
    have hF:= Cacao.steamed h u ((vent _|>.continuous).comp hc) (show Continuous q from (vent _|>.continuous).comp hc) (show Integrable g δ from hz _) (hz _) hp he'; change (∫ x,q x∂δ) = ∫ y,dotProduct (D⁻¹*ᵥy) u*g y∂δ at hF; simp_rw [hu] at hF; rw [integral_sub (hz _) ((show Integrable g δ from hz _).const_mul _), integral_const_mul] at hF; rw [hx (Z'*f), hx f, hx (dint _ _)]; change (∫ y,eval (S y) _∂δ)= F'*(∫ y,g y∂δ)+(∫ y,q y∂δ); linarith only [hF]
end YM.MSbar.Duel
