import YM.MSbar.Duel.Ladle
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
local notation "R"=> SpringK σ
-- concrete directional polynomial partial
local notation "H"=>SpringK σ
local notation "G"=>SpringK ι
local notation "B"=>View τ
variable (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ)(D:Matrix τ τ ℝ) (h:D.PosDef)
local notation "L"=> C'*D*C'.transpose
set_option quotPrecheck false
local notation "ν"=> PowerSeries.map (rail A).toRingHom
open MeasureTheory Set Metric
noncomputable def present (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ) (x: W)(y:B) := A*ᵥx+C'*ᵥy
variable (F: View τ→ℝ)(T: View ι→L[ℝ] View τ)
structure Reef (F: View τ→ℝ) (k:ℕ) : Prop where
     smooth : ContDiff ℝ k F
     cost : Lodge.Curb k F
variable (q:Pot σ)(x:View ι)(hf:Reef F 1)
local notation "ω'"=> fieldLaw D
local notation "Y"=>present A C'
def actor (A: Matrix σ ι ℝ)(C':Matrix σ τ ℝ)(F: View τ→ℝ)(T: View ι→L[ℝ]View τ)(q:Pot σ) (x:View ι)(y:View τ) := MvPolynomial.eval (present A C' x y) q * F (y+T x)
lemma dim_cost (b:ℝ)(hb:0≤b):∃ t:Pot τ,∀ y:View τ,0≤MvPolynomial.eval y t∧∀ x:View ι,‖x‖≤ b→ |MvPolynomial.eval (present A C' x y) q| ≤ MvPolynomial.eval y t:=by
    induction q using MvPolynomial.induction_on with
    | C a=> exact ⟨MvPolynomial.C |a|,fun y=>⟨by rw [eval_C]; exact abs_nonneg _,fun x hx=>by rw [eval_C,eval_C]⟩⟩
    | add p q hp hq=>
          obtain ⟨t,ht⟩:=hp; obtain ⟨u,hu⟩:=hq; refine ⟨t+u,fun y=>?_⟩; simp_rw [_root_.map_add]; exact ⟨add_nonneg (ht y).1 (hu y).1,fun x hx=> (abs_add_le ..).trans (add_le_add (ht y|>.2 x hx) (hu y |>.2 x hx))⟩
    | mul_X p a hp=>
          obtain ⟨t,ht⟩:=hp; let X:= rail C' (MvPolynomial.X a); let Q':= (toLin' A).toContinuousLinearMap; let c:= ‖Q'‖*b; let T:Pot τ:=MvPolynomial.C c+1+X^2; have he(y:B): MvPolynomial.eval y X= (C'*ᵥy) a:=(congr_fun (clearL C' y) (MvPolynomial.X a)).trans (eval_X ..)
          have hc:0 ≤ c:= mul_nonneg (norm_nonneg _) hb
          have hv(x:W)(y:B)(hx:‖x‖≤ b):|Y x y a|≤MvPolynomial.eval y T:=by
                let a':=(C'*ᵥy) a; unfold T; rw [_root_.map_add, _root_.map_add,_root_.map_one,eval_C,_root_.map_pow,he]; change |Q' x a+a'| ≤ c+1+a'^2; apply (abs_add_le ..).trans; apply (add_le_add (show |Q' x a| ≤ c from (norm_le_pi_norm _ _).trans ((Q'.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))) (show |a'| ≤ 1+a'^2 by nlinarith [sq_abs a'])).trans_eq; ring
          refine ⟨t*T,fun i=>?_⟩; rw [_root_.map_mul]; refine ⟨mul_nonneg (ht i).1 ((abs_nonneg _).trans (hv (0:W) i (by rw [norm_zero]; exact hb))),fun x hx=>?_⟩; rw [_root_.map_mul, eval_X,abs_mul]; exact mul_le_mul (ht i|>.2 _ hx) (hv x i hx) (abs_nonneg _) (ht i|>.1)
include hf
lemma actorD : ContDiff ℝ 1 (fun v:W × B=> actor A C' F T q v.1 v.2) :=by
     unfold actor; exact ContDiff.mul (((vent q).of_le le_top).comp (f:=fun v:W × B=>Y v.1 v.2) (((toLin' A).toContinuousLinearMap.contDiff.comp contDiff_fst).add ((toLin' C').toContinuousLinearMap.contDiff.comp contDiff_snd))) ((hf.smooth.of_le (by norm_num)).comp (contDiff_snd.add (T.contDiff.comp contDiff_fst)))
include h
set_option maxHeartbeats 450000 in
lemma fresh : Integrable (actor A C' F T q x) ω':=by
     let W':= actor A C' F T q x; have h': ContDiff ℝ 1 W':= (actorD A C' F T q hf).comp (f:=fun z:B=>(x,z)) (contDiff_const.prodMk (show ContDiff ℝ 1 (@id B) from contDiff_id)); let v(y:B):= MvPolynomial.eval (Y x y) q; have he:Integrable v ω':=(grille C' h q (A*ᵥx) 1 (by norm_num)).integrable le_rfl
     obtain ⟨c,hc,hC⟩:= Lodge.meter hf.smooth hf.cost ([]:List (View τ)) (by simp)
     refine (he.norm.mul_const c).mono' h'.continuous.aestronglyMeasurable (Eventually.of_forall fun y=>?_); change |v y*F _| ≤ ‖v y‖*_; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
variable (u:View ι) (y: View τ)
noncomputable def hPoke (q:Pot σ)(u:View ι)(x:W)(y:B): ℝ:= fderiv ℝ (fun i=>actor A C' F T q i y) x u
noncomputable def tPoke (q:Pot σ)(u:View τ)(x:W)(y:B): ℝ:= fderiv ℝ (actor A C' F T q x) y u
omit h
lemma peaks : hPoke A C' F T q u x y= actor A C' F T (dint (A*ᵥu) q) x y+ MvPolynomial.eval (Y x y) q* fderiv ℝ F (y+T x) (T u):=by
    let L₀:= (toLin' A).toContinuousLinearMap; let V':=(λ i:W=> Y i y); have hP:HasFDerivAt V' L₀ x:= L₀.hasFDerivAt.add_const _; have hu:HasFDerivAt (fun z':W=> y+T z') T x:= T.hasFDerivAt.const_add _; let k:= Y x y; have hq:= (vent q|>.differentiable (by simp) k).hasFDerivAt.comp _ hP; have hv:= (hf.smooth.differentiable (by norm_num) (y+ T x)).hasFDerivAt.comp x (f:=fun z':W=>y+T z') hu; have hx: fderiv ℝ (fun i=>actor A C' F T q i y) x= _:= (hq.mul hv|>.fderiv)
    unfold hPoke; rw [hx]; change MvPolynomial.eval k q*fderiv ℝ F (y+T x) (T u) + F _ *fderiv ℝ (fun v=> MvPolynomial.eval v q) k (L₀ u) = _; rw [dimY]; unfold actor k; rw [show L₀ u=A*ᵥu from rfl]; change _+ F (y+T x)* MvPolynomial.eval (Y x y) (dint (A*ᵥu) q) = _; ring
lemma twinge (u:View τ) : tPoke A C' F T q u x y= actor A C' F T (dint (C'*ᵥu) q) x y+MvPolynomial.eval (Y x y) q*fderiv ℝ F (y+T x) u:=by
    let L₀:=(toLin' C').toContinuousLinearMap; have hP:HasFDerivAt (Y x) L₀ y:= L₀.hasFDerivAt.const_add _; have hu:HasFDerivAt (fun z':B=>z'+T x) (ContinuousLinearMap.id ℝ _) y:=(hasFDerivAt_id ..).add_const _; let k:= Y x y; have hq:= ((vent q).differentiable (by simp) k).hasFDerivAt.comp _ hP; have hv:= (hf.smooth.differentiable (by norm_num) (y+ T x)).hasFDerivAt.comp y (f:=fun z':B=>z'+T x) hu
    unfold tPoke; rw [show fderiv ℝ (actor A C' F T q x) y=_ from (hq.mul hv).fderiv]; change MvPolynomial.eval k q*fderiv ℝ F (y+_) u +F _*fderiv ℝ (fun v=>eval v q) k (L₀ u) = _; rw [dimY]; unfold actor k; rw [show L₀ u=C'*ᵥu from rfl]; ring
end YM.MSbar.Duel
