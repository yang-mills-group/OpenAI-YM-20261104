import YM.MSbar.Duel.Dint
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
noncomputable def bowlD (k:σ→σ→ℝ): Module.End ℝ (Pot σ):= (branc k).choose
noncomputable def oven (k: Matrix σ σ ℝ)(f:H): H:= pulled (bowlD k) f
noncomputable def flux (b:View σ): Module.End ℝ (SpringK σ):= pulled (dint b)
lemma dol (u:P)(b:V)(v:P):dint b (u*v)=dint b u*v+u*dint b v:=by apply MvPolynomial.funext; intro i; simp only [← dimY,_root_.map_add,_root_.map_mul]; rw [fderiv_fun_mul ((vent u).contDiffAt.differentiableAt (by simp)) ((vent v).contDiffAt.differentiableAt (by simp)),_root_.add_apply,_root_.smul_apply,_root_.smul_apply, smul_eq_mul,smul_eq_mul]; ring
lemma chip (b:V)(g f:H):flux b (f*g)=flux b f*g+f*flux b g:= ascent (dint b) (fun x y=> dol x b y) f g
lemma rose (b:V)(f:H)(he:Kind f): flux b (Spring f)=flux b f * Spring f:=springUp f (dint b) (fun x y=> dol x b y) he
lemma nick (k:Matrix σ σ ℝ)(f:H)(b:ℕ): µ b (oven k f)= bowl k (µ b f):=by unfold oven; rw [ride]; exact (branc k).choose_spec _
lemma tone (k:Matrix σ σ ℝ)(f:H)(he:Kind f) : oven k (Spring f) = Spring (confect k f):=by apply PowerSeries.ext; intro m; rw [nick,confect,sunshine ePeak,(airy he).2,PowerSeries.coeff_map, Gallery,PowerSeries.coeff_mk];rfl
variable (β γ:SpringK σ)
local notation "S"=> Spring β
local notation "fA"=> ν (confect L β)
local notation "ϑ"=>oven L
variable (b:ι→ View σ)(M:ι→ View τ)(K: Pot ι)(G₀:ι → Pot σ)
structure Mold (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ)(D:Matrix τ τ ℝ)(b:ι→ View σ)(M:ι→ View τ)(K: Pot ι)(G₀:ι → Pot σ):Prop where
    shift (i:ι): b i+C'*ᵥ M i = A*ᵥ bolt i -- bolt.W
    score (i:ι)(u:View ι)(v:View τ): MvPolynomial.eval (A*ᵥu + C'*ᵥ v) (G₀ i) = - MvPolynomial.eval u ((dint (bolt i)) K)+ dotProduct (D⁻¹ *ᵥ v) (M i)
local notation "Ξ"=>PowerSeries.C
variable (hM:Mold A C' D b M K G₀)
include hM h
-- differential identity for quotient.
lemma organ (i:ι)(p:H) : ν (oven L (flux (b i) p+Ξ (G₀ i)*p))=flux (bolt i) (ν (oven L p)) - Ξ (dint (bolt i) K)*(ν (oven L p)):=by
    apply PowerSeries.ext; intro m; let F:=µ m p; let u:= b i; let m':=M i
    obtain ⟨f,hf⟩:=branc L; rw [PowerSeries.coeff_map, flux, nick, _root_.map_add, ride, PowerSeries.coeff_C_mul, ← hf, _root_.map_add,hf,hf,_root_.map_add, _root_.map_sub, flux, ride,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,nick]; apply MvPolynomial.funext; intro x; rw [_root_.map_add, _root_.map_sub, _root_.map_mul]
    have he(v:P): MvPolynomial.eval x (rail A v)=eval (A *ᵥ x) v:= congr_fun (clearL A x) v; change MvPolynomial.eval x (rail A (bowl L (dint _ F)))+eval x (rail A _) = MvPolynomial.eval x (dint (bolt i) (rail A (bowl L F))) - MvPolynomial.eval x _ * MvPolynomial.eval x (rail A _); rw [dimK (bowl L F) A (bolt i)]
    rw [he,he,he,he,incomes _ (A*ᵥx) C' h _ (-eval x (dint (bolt i) K)) _ (hM.score i x)]; rw [← hM.shift i, desS  (b i) F L,  desS (C'*ᵥm') F L,dime,_root_.map_add];ring
omit hM h
noncomputable def batt (b:ι→View σ)(K:ι→SpringK σ) : List ι → SpringK σ
  | []=>1
  | i::l=> flux (b i) (batt b K l)+ K i*batt b K l
noncomputable def readScore (b:ι→View σ)(G₀:ι→Pot σ)(β:SpringK σ) := batt b (fun i=> Ξ (G₀ i)+flux (b i) β)
-- output log horizontal term
noncomputable def port (K:Pot ι)(f:SpringK ι) : List ι → SpringK ι := batt (fun i=> Uniform.bolt i) (fun i=> -PowerSeries.C (dint (bolt i) K)+flux (bolt i) f)
variable (hP:Kind β)
include hM h hP
lemma orbit (l:List ι): ν (oven L (readScore b G₀ β l * Spring β))= port K (ν (confect L β)) l * Spring (ν (confect L β)) :=by
    let f:= fA; let V₁:= port K f; let v:= readScore b G₀ β; have ht : Kind f:=by unfold f Kind; rw [PowerSeries.coeff_map,sugar _ hP,_root_.map_zero]
    induction l with
    | nil=> change ν (oven L ((1:H)*_)) = (1:G)*_; rw [one_mul,tone _ _ hP,sunshine (_ : P →ₐ[ℝ] Q),one_mul]
    | cons i l ih=>
       let g:=v l *Spring β; let d:=flux (bolt i:W); have h₀:v (i::l)*Spring β=flux (b i) g+ Ξ (G₀ i)*g:=by change ((flux (b i) (v l))+_ *v l) *S= _; unfold g; rw [chip,rose (b i) β hP];ring
       change ν (oven L (v (i::l)*_)) = V₁ (i::l)* _; rw [h₀,organ A C' D h b M K G₀ hM i g,show ν (oven L g)= V₁ l* Spring f from ih, chip, rose _ f ht]; change _= (d (V₁ l)+ (-Ξ (dint (bolt i) K) + d f)*(V₁ l))*Spring f; unfold d; ring -- _ placeholders
end YM.MSbar.Duel
