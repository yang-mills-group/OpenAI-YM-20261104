import YM.MSbar.Cacao.Acre
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open MeasureTheory Filter Function Finset Matrix PowerSeries
open ProbabilityTheory MvPolynomial Polynomial
open scoped Topology BigOperators Classical
variable {σ ι : Type} [Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ]
open Further.GaussianScalar
local notation "H"=> View ι
local notation "V"=> View σ
local notation "P"=> Pot σ
variable (k:σ→σ→ℝ)
lemma pearl_vector : ∃ t: P→ₗ[ℝ]Ball σ, ∀ j,t j= pearl k j:=by
    let t:P→ₗ[ℝ]Ball σ:= {
        toFun:=pearl k
        map_add' x y:= Polynomial.ext fun i=>by simp_rw [Polynomial.coeff_add, season,pour,_root_.map_add, smul_add]
        map_smul' r x:= Polynomial.ext fun i=>by simp_rw [RingHom.id_apply,Polynomial.coeff_smul,season,pour,_root_.map_smul]; rw [smul_comm] }
    exact ⟨t,fun _=> rfl⟩
lemma vip (i:σ)(p:P): bowl k ((tureen k i) p)= tureen k i (bowl k p):=by
    have he : (pearl k ((tureen k i) p))=elevatorP (tureen k i) (pearl k p):=by
       apply Polynomial.ext; intro n; change _= Polynomial.coeff (rideP (tureen k i) _) n; simp only [riseP,season,pour,map_smul,gradient]
    unfold bowl; rw [he,slipE _ _]
noncomputable def ePeak : (Ball σ)→ₐ[ℝ](Pot σ) := (Polynomial.aeval (R:=Pot σ) (1:Pot σ)).restrictScalars ℝ
lemma peal (p:Ball σ): ePeak p=Polynomial.eval 1 p:=rfl
lemma branc (k:σ→σ→ℝ) : ∃ t : P→ₗ[ℝ]Pot σ,∀ j,t j=bowl k j:=by
    obtain ⟨T,h⟩:=pearl_vector k; exact ⟨ePeak.toLinearMap.comp T,fun x=>by change ePeak (T x)= _; rw [h,peal]; rfl⟩
variable {g : Matrix ι ι ℝ} (v:Matrix σ ι ℝ) (x:View σ) (h:g.PosDef)
set_option quotPrecheck false
local notation "KF"=> v*g*v.transpose
local notation "ζ"=> (fun r:View ι=> x+v *ᵥ r)
local notation "μ!"=> fieldLaw g
def Summer (g : Matrix ι ι ℝ)(v:Matrix σ ι ℝ)(x:View σ)(p:Pot σ) := MvPolynomial.eval x (bowl (v*g*v.transpose) p)=∫ r:View ι,MvPolynomial.eval (x+v *ᵥ r) p ∂fieldLaw g
local notation "S"=> Summer g v x
include h
lemma veranda : ∃ A: Submodule ℝ P,∀ j:P,j∈A ↔ Summer g v x j:=by
    obtain ⟨T,hT⟩:=branc (KF)
    let u(p:P)(r:H):=MvPolynomial.eval (ζ r) p; have hi(p:P): Integrable (u p) μ! :=(grille v h p x 1 (by simp)).integrable le_rfl
    let Z:P→ₗ[ℝ]ℝ:= {
        toFun:=fun p=> ∫ r,u p r∂fieldLaw g
        map_add' u' v':=by simp_rw [u,_root_.map_add]; exact integral_add (hi u') (hi v')
        map_smul' r p:=by simp_rw [u,← MvPolynomial.C_mul',_root_.map_mul,MvPolynomial.eval_C, integral_const_mul]; rfl }
    let L:=(MvPolynomial.aeval (R:=ℝ) x).toLinearMap.comp T - Z; refine ⟨LinearMap.ker L,fun j=>?_⟩; rw [LinearMap.mem_ker,show L j= MvPolynomial.eval x (bowl (KF) j)-∫ z,u j z∂μ! from ?_,sub_eq_zero]; · rfl
    rw [←hT];rfl
omit h in
noncomputable def spore : List σ→ Module.End ℝ P
   | []=>LinearMap.id
   | i::L=> (spore L).comp ((pderiv i).toLinearMap)
lemma seen (u:P): Summer g v x u:=by
    let k:σ→σ→ℝ:= KF; obtain ⟨A,H₀⟩:=veranda v x h
    have hC: 1∈ A:=by
       rw [H₀]; unfold Summer bowl; rw [stop k]; simp
    have hX (i:σ) (p:P) (hv:p∈ A)(hh:∀ j, pderiv j p∈A) : p*MvPolynomial.X i∈ A:=by
       have hf := (H₀ p).1 hv; rw [H₀]
       have h : tureen k i p∈ A:=by rw [drink]; exact A.sum_mem (fun i _=> A.smul_mem _ (hh i));
       have ht := (H₀ _).1 h; unfold Summer at *; rw [peas v ‹_›,spout k p i (trunk v ‹_›), _root_.map_add,_root_.map_mul,MvPolynomial.eval_X, hf,←vip k i p,ht]
    suffices h :∀ L:List σ,spore L u ∈ A from (H₀ u).1 (h [])
    induction u using MvPolynomial.induction_on with
    | C a=> intro L; cases L with
                        | nil=> apply (show spore [] (MvPolynomial.C a)= a • (1:P) from ?_).symm ▸ (A.smul_mem a hC); rw [show a • (1:P)= MvPolynomial.C a from by rw [← MvPolynomial.C_mul',mul_one]]; rfl
                        | cons i L=> change spore L (pderiv i (MvPolynomial.C a))∈A; rw [pderiv_C,_root_.map_zero]; exact A.zero_mem
    | add p q hp hq=> intro i; rw [_root_.map_add]; exact A.add_mem (hp _) (hq _)
    | mul_X p c hp=>
       have ht :∀ (L:List σ)(p:P),(∀ j:List σ, spore j p∈ A)→ spore L (p*MvPolynomial.X c)∈A:=by
           intro L; induction L with
           | nil=> intro p he; exact hX c p (he []) (fun i=> he [i])
           | cons i L IH=>
             intro p hp; change spore L (pderiv i (p* MvPolynomial.X c:P))∈ _; rw [pderiv_mul,_root_.map_add]; by_cases hx:i=c
             · rw [hx,pderiv_X_self,mul_one]; exact A.add_mem (IH _ (fun L=> hp (c::L))) (hp L)
             rw [pderiv_X_of_ne (Ne.symm hx),mul_zero,_root_.map_zero, add_zero]; exact IH _ (fun L=>hp (i::L))
       exact fun i=> ht i p hp
-- exponential.W.R.Full
noncomputable def confect (k:σ→σ→ℝ)(f:PowerSeries (Pot σ)) : PowerSeries (Pot σ):= PowerSeries.map ePeak.toRingHom (normalized k f)
omit h in
lemma sugar {f:PowerSeries (Pot σ)} (hf: Kind f): Kind (confect k f) := by unfold Kind confect; rw [PowerSeries.coeff_map,(airy hf).1,_root_.map_zero]
lemma goodie {f:PowerSeries (Pot σ)} (hf: Kind f)(i:ℕ):MvPolynomial.eval x (PowerSeries.coeff i (Spring (confect (v*g*v.transpose) f)))=(∫ z:View ι,MvPolynomial.eval (x+v *ᵥ z) (PowerSeries.coeff i (Spring f))∂fieldLaw g) := by
   unfold confect; rw [sunshine ePeak,(airy hf).2,PowerSeries.coeff_map,Gallery,PowerSeries.coeff_mk]; exact seen v x h _
end YM.MSbar.Cacao
