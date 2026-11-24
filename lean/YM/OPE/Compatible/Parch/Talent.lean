import YM.OPE.Compatible.Parch.Trees
import YM.OPE.Compatible.Parch.Grove
/-!
# Dynamic neatness budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver Flume.Page
open Drift Char Silt Silt.Float Module Variance Merchant Merchant.Prom Tensor
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}{o:Cover}
section Volt
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
noncomputable abbrev Dallas (g:E→ℝ)(d:ℕ)(b:ℝ):Prop:= ∀ x:Fin d→E,(∀ i,‖x i‖≤1)→ ‖coeff g d 0 x‖ ≤ b
lemma glimpse (n:ℕ):∃ c:ℝ,0 ≤ c∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](g:E→ℝ),ContDiffAt ℝ ω g 0 → ∀ t:ℝ,LimitR t (Claw.rank g n)→ Dallas g n (c*t):=by
       obtain ⟨C,K,hC,hK,H⟩:=Flume.Script.limelight n; let T:= K+1; have ht:0<T:=add_pos_of_nonneg_of_pos hK zero_lt_one; refine ⟨C*T^n,mul_nonneg hC (pow_nonneg ht.le _),fun E _ _ g hx t hv=>?_⟩; let A:=coeff g n 0; have hg:0≤t:= (norm_nonneg _).trans (hv 0 (by rw[norm_zero];exact zero_le_one)); unfold Dallas; rw [mul_assoc]; refine H E A _ (coeff_symm (hx.of_le le_top)) (mul_nonneg (pow_nonneg ht.le _) hg) (fun v h=>?_)
       let z:= T⁻¹ • v; have he:z=T⁻¹ • v:=rfl; have hz:‖z‖≤1:=by rw [he,norm_smul,norm_inv,Real.norm_of_nonneg ht.le]; exact (mul_le_mul_of_nonneg_left (h.trans (le_add_of_nonneg_right zero_le_one)) (inv_nonneg.mpr ht.le)).trans_eq (inv_mul_cancel₀ ht.ne')
       rw[← show T • z=v from smul_inv_smul₀ ht.ne' _,Tensor.homogeneous,norm_smul, norm_pow,Real.norm_of_nonneg ht.le]; exact mul_le_mul_of_nonneg_left (hv z hz) (pow_nonneg ht.le _)
lemma Dollar {p:T E ℝ r}{C:ℝ}(he:0≤C)(h:∀ x: Fin r→E,(∀ i,‖x i‖≤1)→ ‖p x‖≤ C): ‖p‖≤ C:=by
       refine ContinuousMultilinearMap.opNorm_le_bound he (fun x=>?_); let y(i):=x i; by_cases hx:∃ i,x i=0
       · obtain ⟨i,hi⟩:=hx; rw [p.map_coord_zero i hi,norm_zero]; exact mul_nonneg he (prod_nonneg fun _ _=>norm_nonneg _)
       let f(i:Fin r):=‖x i‖; have hv(i):0<f i:=norm_pos_iff.mpr (fun h=>hx ⟨i,h⟩); let z(i:Fin r):= (f i)⁻¹ • x i; have hZ(i):‖z i‖=1:=by unfold z; rw [norm_smul,norm_inv,Real.norm_of_nonneg (hv i).le,inv_mul_cancel₀ (hv i).ne'] -- ok
       rw [show p x=(∏ i,f i) • p z from ?_,norm_smul,Real.norm_of_nonneg (prod_nonneg fun i _=>(hv i).le), mul_comm]; rotate_left; · nth_rw 1 [show x=(fun i=> f i • z i) from funext fun i=> (smul_inv_smul₀ (hv i).ne' _).symm]; exact p.map_smul_univ ..
       exact mul_le_mul_of_nonneg_right (h _ (fun i=> (hZ i).le)) (prod_nonneg fun i _=>(hv i).le)
lemma Willow {g:E→ℝ} {t:ℝ} (h:Dallas g i t): ‖iteratedFDeriv ℝ i g 0‖ ≤ t* i.factorial:=by
       have ht:=Dollar ((norm_nonneg _).trans (h 0 (fun _=> by simp))) h; rw [coeff,norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_eq_div] at ht; exact (div_le_iff₀ (by positivity)).mp ht
end Volt
section
variable {I:Type}{E:I→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)](p:(i:I)→ E i→ℝ) {φ:Filter I}{Γ:I→ℝ}(h:Tendsto Γ φ atTop)
include h
lemma Breeze {T:(i:I)→ E i→ℝ}(hT:Bills φ Γ T)(hv:∀ᶠ i in φ,Tall (T i) d) (k:ℕ): Bills φ Γ (fun i=>Claw.rank (T i) k):= by
        by_cases he:k ≤ d; exact Bills.rankFee h hT hv he
        refine (Bills.zeroB (E:=E) (F:=fun _=>ℝ) h).merge (hv.mono fun i hi=>?_); obtain ⟨P,hP⟩:=hi.stock; exact ((Tall.wing P hP k).trans (if_neg he)).symm
lemma blissP (hv:Bills φ Γ (fun i=>Claw.rank (p i) k))(hx:∀ᶠ i in φ,ContDiffAt ℝ ω (p i) 0) : ∃ c:I→ℝ,RateLE φ Γ c 0 ∧ ∀ᶠ i in φ,Dallas (p i) k (c i):=by
       obtain ⟨s,hs,H⟩:= glimpse k; obtain ⟨b,hb,hT⟩:=hv; exact ⟨_,((RateLE.const s h).mul hb).mono (by norm_num),(hx.and hT).mono fun i hi=>H _ _ hi.1 _ hi.2⟩
lemma Floral (hv:Bills φ Γ p)(hx:∀ᶠ i in φ,Tall (p i) d)(j:ℕ): RateLE φ Γ (fun i=>‖iteratedFDeriv ℝ j (p i) 0‖) 0:=by
       obtain ⟨t,ht,H⟩:=blissP p h (Breeze h hv hx j) (hx.mono fun i hi=> (Tall.neat hi).contDiffAt); refine ((ht.mul (RateLE.const (j.factorial:ℝ) h)).of_norm_le (H.mono (fun i hi=> (?_:‖(‖iteratedFDeriv ℝ j (p i) 0‖)‖≤ _ )))).mono (by norm_num)
       rw [Real.norm_of_nonneg (norm_nonneg _)]; exact Willow hi
end
end YM.OPE.Claw
