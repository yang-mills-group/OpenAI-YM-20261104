import YM.OPE.Compatible.Parch.Parcel
/-!
# Work units. Polynomial direction. All estimates pre-mean.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Finset Tensor
open PertExtension Series GaussianScore Libra ScriptJ Variance Cascade Merchant Merchant.SiteL
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {i j r d m k l:ℕ}
section
variable {X E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
open FoldU
lemma clampT {P:T E ℝ r}{c:ℝ}(hp:∀ x:Fin r→ E,(∀ i, ‖x i‖≤1)→ ‖P x‖ ≤ c){t:ℝ}(he:0<t)(x:Fin r→ E)(hx:∀ i, ‖x i‖ ≤ t): ‖P x‖ ≤ t^r * c:=by
      let u(i):=t⁻¹ • x i; have hy(i):‖u i‖≤1:=by unfold u; rw [norm_smul,norm_inv,Real.norm_of_nonneg he.le]; exact (mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr he.le)).trans_eq (inv_mul_cancel₀ he.ne')
      rw[show P x=t^r*P u from ?_, norm_mul, norm_pow,Real.norm_of_nonneg he.le]; refine mul_le_mul_of_nonneg_left (hp u hy) (pow_nonneg he.le _); nth_rw 1 [show x=fun i=> t • u i from funext fun i=> (smul_inv_smul₀ he.ne' _).symm]; erw [P.map_smul_univ (fun i=>t) u];simp
local notation "J'"=> Fin (r+1)
lemma popper {P:T E ℝ (r+1)}{c:ℝ}(hp:∀ x:J'→ E,(∀ i, ‖x i‖≤1)→ ‖P x‖ ≤ c){t:ℝ}(he:0<t)(x y z:E)(hx:‖x‖≤t)(hy:‖y‖≤t)(hz:‖z‖≤t): ‖pop P x y z‖ ≤ (r+1:ℕ)* (t^(r+1)*c) :=by
       have hq(i:J')(j:J'): ‖tab x y i z j‖ ≤ t:=by unfold tab; by_cases ht:j=i; subst j; simpa; rw [update_of_ne ht, banner,rowP]; split_ifs<;> assumption
       change ‖∑ i:J',P (tab _ _ i z)‖≤_; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> clampT hp he _ (hq i))).trans_eq (by simp : ∑ _i∈(univ:Finset J'), t^(r+1)*c=(_ :ℝ)))
variable [FiniteDimensional ℝ E]
lemma smoothI {P:Law E}{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](f:X→ E) (h:∀ y:E,ContDiff ℝ ω fun x=>P.P (f x) y): ContDiff ℝ ω f:=by
       let b:= Module.finBasis ℝ E; have hp(j): ContDiff ℝ ω (fun z:X=> b.coord j (f z)):=by
            let p:= P.inverse (b.coord j)
            have hx(x:X):b.coord j (f x)=P.P (f x) p:=by rw[P.turns];unfold p;rw [Law.applies]
            simp_rw [hx]; apply h
       rw [show f=(fun x=> ∑ i: Fin (Module.finrank ℝ E), b.coord i (f x) • b i) from funext fun i=>(b.sum_repr ..).symm]; refine ContDiff.sum fun i _=>?_ ; exact (hp i).smul contDiff_const
omit [FiniteDimensional ℝ E] in lemma supK {V: E→ₗ[ℝ] ℝ}{a:ℝ}(_ha:0 ≤ a) (h:LimitR a (fun x=>V x)) (x:E): V x ≤ a*‖x‖:=by
       by_cases hx:x=0; subst x; simp
       let t:=‖x‖; have hp:0<t:= norm_pos_iff.mpr hx; let y:= t⁻¹ • x; have he:x=t • y:=(smul_inv_smul₀ hp.ne' _).symm; have hv:‖y‖ ≤1:=by unfold y; rw [norm_smul, norm_inv,Real.norm_of_nonneg hp.le, inv_mul_cancel₀ hp.ne']
       calc
             V x=t* V y:=by nth_rw 1 [he]; rw [map_smul,smul_eq_mul]
             _ ≤ t*a:=mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans (h y hv)) hp.le
             _ = _:=mul_comm ..
lemma pinL {L:Law E}{κ:ℝ}(h:0<κ)(he:∀ x:E,κ*‖x‖^2 ≤ L.P x x)(F: Dual' E)(v:ℝ)(hv:0≤v)(ht:LimitR v ⇑F): ‖L.inverse F‖ ≤ v/κ:=by
     let x:=L.inverse F; have hz:L.P x=F:=Law.applies ..; by_cases hp:x=0; swap
     · have hf:0 < ‖x‖:=norm_pos_iff.mpr hp; have hh:κ*‖x‖^2 ≤ v*‖x‖:= (he x).trans ((DFunLike.congr_fun hz x).trans_le (supK hv ht _)); rw [le_div_iff₀ h]; change ‖x‖*κ ≤ v; apply le_of_mul_le_mul_right _ hf; linarith only [hh]
     change ‖x‖≤_;rw[hp,norm_zero]; exact div_nonneg hv h.le
end
end YM.OPE.Claw
