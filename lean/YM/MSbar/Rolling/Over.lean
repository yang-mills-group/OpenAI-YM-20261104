import YM.MSbar.Rolling.Tapes
import YM.MSbar.Kelvin.Mead
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Cacao Bakery MvPolynomial Price
open Further.GaussianScalar Portal
open scoped Topology Classical BigOperators ContDiff
variable {ι σ V:Type}[Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ]
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "H"=>View ι
local notation "L"=> Rolling.fuel
variable (A:Matrix ι σ ℝ){K:Matrix σ σ ℝ}{B:ℝ}
local notation "V₀"=>View σ
variable (hK:K.PosDef)
local notation "λ!"=>fieldLaw
-- arbitrary inequalities.In.Fxn
variable {μ:Measure (View σ)} [IsProbabilityMeasure μ]
lemma cats (p:View σ → ℝ)(t:ℝ) (ht:0<t)(h:Integrable p μ)(he:Integrable (fun x=>p x^2) μ) (X:Set V₀)(hx:MeasurableSet X) : ‖∫ i in X,p i∂ μ‖≤ μ.real X/t+t*(∫ i,p i^2∂μ):=by
   let q(x):=p x^2; apply (norm_integral_le_integral_norm p).trans; rw [←integral_const_mul]; have hh(X):IntegrableOn (fun i=>1/t+t*q i) X μ:= (show Integrable (fun i=>1/t+t*q i) μ from (integrable_const _).add (he.const_mul _)).integrableOn; refine (setIntegral_mono_on h.integrableOn.norm (hh _) hx (fun i hi=>?_)).trans ?_
   · calc ‖p i‖ ≤ 1/t+t*(‖p i‖^2) := by apply le_of_mul_le_mul_left (a:=t) _ ht; rw [mul_add,one_div,mul_inv_cancel₀ ht.ne']; nlinarith only [sq_nonneg (1-t*‖p i‖),mul_nonneg ht.le (norm_nonneg (p i))]
          _ = _ := by simp [Real.norm_eq_abs,q]
   rw [integral_add (integrable_const _) (he.const_mul _|>.integrableOn),setIntegral_const,smul_eq_mul,mul_one_div]; apply add_le_add le_rfl; exact setIntegral_le_integral (he.const_mul t) (ae_of_all _ (fun x=>mul_nonneg ht.le (sq_nonneg (p x))))
include hK
lemma dawnM(p:ℕ): Price (fun x (_:Unit)=>True) p (fun x _=> (fieldLaw K).real {i:V₀| Rolling.fuel x < ‖i‖}):=by
   let W:= ∑ i,|K i i|; have hp(i): K i i ≤ W:= (le_abs_self _).trans (Finset.single_le_sum (f:=fun i=>|K i i|) (fun i _=>abs_nonneg _) (Finset.mem_univ i)); let A:ℝ:=p; let c:=W*A^2/2; let D:=2*Fintype.card σ* Real.exp c; let Z(x):= λ! K |>.real {i:V₀| x < ‖i‖}; apply fixed 0 D; filter_upwards [width] with x ⟨hx,he,hV⟩ y _
   let X : Set V₀:= {i |L x< ‖i‖}; let Q(j:σ):Set V₀:={i|L x < |i j|}; have hk:X ⊆⋃ i∈(Finset.univ:Finset σ), Q i:=by
       intro i hi; by_contra! hG; have hp' (j:σ):‖i j‖ ≤ L x:=le_of_not_gt (fun hh=> hG (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,hh⟩⟩)); exact not_lt_of_ge ((pi_norm_le_iff_of_nonneg (zero_le_one.trans hV)).mpr hp') hi
   let v:=-(A*L x)+c; have hh : (fieldLaw K).real X ≤ ∑ i:σ, 2 * Real.exp v := ((measureReal_mono hk (by simp)).trans (measureReal_biUnion_finset_le _ _)).trans (Finset.sum_le_sum fun i _=> Kelvin.chorus hK W hp i (L x) A (Nat.cast_nonneg _))
   -- simplify
   rw [Real.norm_of_nonneg measureReal_nonneg,pow_zero,mul_one]; apply hh.trans_eq; unfold v D Rolling.fuel; rw [Real.log_inv, mul_neg,neg_neg,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Real.exp_add,show Real.exp (A *Real.log x)=x^p from ?_]; ring
   unfold A; rw [Real.exp_nat_mul,Real.exp_log hx]
-- polynomial integrals. heat proof.Seen
local notation "µₛ"=>fieldLaw K
variable {Z:ℝ→V→Prop}{Ψ:ℝ→V→View ι}
set_option quotPrecheck false
local notation "η(t" t ", " k ")"=> (fun v:View σ=> Ψ t k+A *ᵥ v)
variable {p:ℕ} (f:PowerSeries (Pot ι))
lemma adapts (x:View ι)(t:ℝ)(p:ℕ): Integrable (fun v:View σ=> taste p (picture (x+A *ᵥ v) f) t) (fieldLaw K):= by unfold taste; apply integrable_finsetSum; intro i _; unfold picture; simp_rw [PowerSeries.coeff_map]; exact ((grille A hK _ _ 1 (by norm_num)).integrable le_rfl).const_mul _
variable {X:ℝ→V→Set (View σ)}(hp : Price Z 0 Ψ)(hv:∀ᶠ t in Γ,∀ x,Z t x → {v:View σ| ‖v‖ ≤ Rolling.fuel t}⊆ X t x∧MeasurableSet (X t x))
include hp hv
lemma squirt (D:Pot ι): Price Z p (fun t x=>∫ v in (X t x)ᶜ,eval (η(t t, x) v) D ∂fieldLaw K):=by
    let F(t:ℝ)(x:V)(v):=eval (η(t t, x) v) D; let m₀(t)(x):=∫ i:View σ,(F t x i)^2∂µₛ
    have hx:Price Z 0 m₀:= by
        refine (volley Ψ hp (bowl (A*K*A.transpose) (D^2))).egress (Eventually.of_forall (fun t x he=>?_)); have hV:= seen A (Ψ t x) hK (D^2); unfold Summer at hV; unfold m₀ F; simpa only [map_pow] using hV -- V
    let μ':=(fun t:ℝ=> (fieldLaw K).real {v:V₀|Rolling.fuel t < ‖v‖})
    obtain ⟨R,hR⟩:=dawnM hK (2*p); have hb:Price Z p (fun t x=> μ' t/t^p):=by
        refine ⟨R,?_⟩; filter_upwards [width,hR] with x ⟨hx,he,hT⟩ hh i _; let a:=μ' x; rw [norm_div,Real.norm_of_nonneg (pow_nonneg hx.le _),div_le_iff₀ (pow_pos hx p)]
        exact (hh () trivial).trans_eq (by ring)
    refine (hb.nsum ((xrise Z p).product hx)).bounds ?_; filter_upwards [width,hv] with t ⟨hx,hT,hR⟩ he v hs; apply (cats (F t v) (t^p) (pow_pos hx _) ((grille A hK D _ 1 (by norm_num)).integrable le_rfl) _ _ (he v hs).2.compl).trans
    · apply le_trans (add_le_add _ (le_refl (t^p*m₀ t v))) (le_abs_self _); apply div_le_div_of_nonneg_right _ (pow_nonneg hx.le p); refine measureReal_mono (fun i hi=>(show Rolling.fuel t < ‖i‖ from lt_of_not_ge (fun hz=> hi ((he v hs).1 hz)))) (by simp)
    let W:= ((grille A hK (D^2) (Ψ t v) 1 (by norm_num)).integrable le_rfl); simpa only [map_pow] using W -- F defeq?
lemma mort (N p:ℕ) : Price Z p (fun t x => ∫ v in (X t x)ᶜ,taste N (picture (η(t t, x) v) f) t ∂fieldLaw K):=by
    let G'(i)(t:ℝ)(x:V) := ∫ v in (X t x)ᶜ,eval (η(t t, x) v) (PowerSeries.coeff i f)∂µₛ
    refine (Price.bag (Finset.range (N+1)) (fun i t x=>t^i*G' i t x) (fun i _=>?_)).egress (Eventually.of_forall fun t x he=>?_)
    · exact (((xrise Z i).product (q:=p) (squirt A hK hp hv _)).poorly (by omega))
    unfold taste picture; simp_rw [PowerSeries.coeff_map]; rw [integral_finsetSum]; apply Finset.sum_congr rfl; intro i _; rw [integral_const_mul]; exact fun i _=> show Integrable (fun v:View σ=> _) _ from (((grille A hK _ (Ψ t x) 1 (by norm_num)).integrable le_rfl).const_mul (t^i)).integrableOn
end YM.MSbar.Rolling
