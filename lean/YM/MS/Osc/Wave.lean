import YM.MS.Osc.Delta
/-!
# Integration along moving lines with phase v:E→ℂ. Domain E finite, IR mass λ.Travel.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Osc
open Set Filter Function Finset Metric MeasureTheory Real
open scoped Topology ContDiff
variable {I J E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
  [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] {μ:I→Measure E} {μs:Measure E}{C:ℝ} {S: Scale I}
  {d k:ℕ}{i:I}{T:I→E}{x g w:I→ℝ}{f:I→ E× F→ ℂ}{U:I→ E→ℂ} {z:E→ℂ}
structure Peak (F:E→ℂ) : Prop where
   pays (x:E): ‖F x‖ ≤1
   shore: Continuous F
-- norm multiplies only budget
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma Vmajor (h:Peak z) {f:E→F→ℂ}(ht:Majorant μs f) : Majorant μs (fun i p=> z i * f i p) := by
    have he (j:ℕ)(p:F): ∀ᵐ i ∂μs,iteratedFDeriv ℝ j (fun x:F=> z i * f i x) p= z i • iteratedFDeriv ℝ j (f i) p := ht.smooth.mono fun i hi=> iteratedFDeriv_const_smul_apply (a:=z i) ( hi.contDiffAt.of_le (by exact_mod_cast le_top))
    refine ⟨ ht.smooth.mono (fun i hi=> contDiff_const.mul hi), fun j p=> ?_, ?_⟩; · exact (h.shore.aestronglyMeasurable.smul (ht.borel j p)).congr ((he j p).mono fun _ h=> h.symm) -- orientation
    intro j p; obtain ⟨v,hv,u,hu,hT⟩:= ht.major j p; refine ⟨v,hv,u,hu,?_⟩; filter_upwards [ hT, ht.smooth ] with i hi hz q hq; rw [ show iteratedFDeriv ℝ j (fun x:F=> z i* f i x) q= z i • iteratedFDeriv ℝ j (f i) q from iteratedFDeriv_const_smul_apply (a:=z i) (hz.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h.pays _)).trans (hi q hq)
abbrev glob (S:Scale I) (μ:I→Measure E) (d:ℕ) : Prop:= Reserve S (fun _=> Set.univ) μ d
def waveInt (U:I→E→ℂ)(μ:I→Measure E)(f:I→ E× F→ℂ)(i:I)(p:F): ℂ:= ∫ q, U i q*f i (q,p) ∂μ i
variable (hU:∀ i, Peak (U i))(H:glob S μ d)(hx:pole S f x)
include hU hx H
lemma rayTag (i:I): Majorant (μ i) (fun q p=> U i q * f i (q,p)):= Vmajor (hU i) (hx.major H i)
lemma Wavepay (h:S.full.Le (fun i (_:F)=>∫ q,S.dust d i q ∂μ i) (fun i _=>g i)): Bound S (waveInt U μ f) (fun i=> x i*g i):= by
    refine ⟨fun i=>(rayTag hU H hx i).contDiff,fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= hx.dominates j d; obtain ⟨D,hD,l,hD'⟩:=h; refine ⟨C*D,by positivity,k+l,fun i p hp=>?_⟩; let Z:=C*S.full.cheap i p^k*(x i*S.length i^j); have hz:= zprice H (sane hx i) hC (k:=k) (j:=j) (p:=p); dsimp only; rw [show waveInt U μ f i=(fun p=>∫ q, U i q*f i (q,p) ∂μ i) from rfl,(rayTag hU H hx i).identity]; apply (norm_integral_le_of_norm_le ((H.integrable i).const_mul Z) ?_).trans
    · rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left (hD' i p hp) hz).trans ?_ -- invalid
      dsimp only; rw [pow_add]; ring_nf; rfl
    refine Filter.Eventually.of_forall fun q:E=>?_ ; have hT:ContDiff ℝ ∞ (fun w:F=> f i (q,w)):= (hx.smooth i).comp (f:=fun w:F=>(q,w)) (by fun_prop)
    rw [ show iteratedFDeriv ℝ j (fun w:F=> U i q*f i (q,w)) p=_ from iteratedFDeriv_const_smul_apply (a:=U i q) (hT.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) ((hU i).pays q)).trans (hk i q p trivial)
where
 zprice {p:F}{k j:ℕ}(_h:glob S μ d){i:I}{C:ℝ}(hN:0≤x i)(hC:0<C): 0≤ C*S.full.cheap i p^k *(x i*S.length i^j):= by have ht:= S.full.cheap_pos (p:=p) (i:=i) (Set.mem_univ _); have hz:= S.pos i; positivity
variable {V:I→ℂ}
omit hU hx H
abbrev Equ (μ:Measure E)(x:E): Prop:= MeasurePreserving (fun i:E=>x+i) μ μ
include hU H hx
lemma windCost (hV:∀ i x,U i (x-T i)=V i* U i x)(h:∀ i,S.length i * ‖T i‖ ≤ C)(hc:0≤ C)(hh:∀ i,Equ (μ i) (T i))(i:I)(p:F) : (1-V i)*waveInt U μ f i p= waveInt U μ (shift T f) i p:= by
   let M:=( μ i ); let y:= T i; unfold waveInt; let F q:=U i q*f i (q,p); let D q :=U i q*f i (q+y,p); have hf: Integrable F M:=(rayTag hU H hx i).values p; have hT : Integrable D M:= by simpa only [Prod.mk_add_mk, add_zero] using (rayTag hU H ( speed hx h hc ) i ).values p
   unfold shift; simp_rw [Prod.mk_add_mk,add_zero,mul_sub]; rw [integral_sub hf hT,sub_mul,one_mul]; congr 1; rw [← integral_const_mul]; symm; let τ: E≃ᵐ E:= MeasurableEquiv.addLeft y; rw [ ← (show MeasurePreserving τ M M from hh i).symm.integral_comp']; refine integral_congr_ae (Filter.Eventually.of_forall fun q=>?_); -- orientation? RHS comp powers etc
   change U i (τ.symm q)* f i (τ.symm q+T i,p)=_; rw [show τ.symm q=q-T i from ?_, sub_add_cancel,hV, mul_assoc]; change -T i+q = q-T i; abel
-- budget for inverse factor by constant.Cut0
lemma rapid_pay (hV:∀ i x,U i (x-T i)=V i* U i x)(h:∀ i,S.length i* ‖T i‖≤ C)(hc:0≤ C)(hh:∀ i,Equ (μ i) (T i))(hw:∀ i,‖T i‖≤ w i)(ε:ℝ)(he:0<ε)(hp:∀ i, ε ≤ ‖1- V i‖)(ht:S.full.Le (fun i (_:F)=>∫ q,S.dust d i q ∂μ i) (fun i _=>g i))(k:ℕ): Bound S (waveInt U μ f) (fun i=> x i*g i*(S.length i*w i)^k):= by
    induction k generalizing f x with
    | zero=> simpa using Wavepay hU H hx ht
    | succ k ih=>
       let Z:=shift T f; have hZ : pole S Z (fun i=> x i*( S.length i*w i)):= (step hx h hc).monotone (Cost.of_le (fun i _ _=> by have hx:=sane hx i; have hs:=S.pos i; gcongr; exact hw i));
       have hz : Bound S (fun i (_:F)=> (1-V i)⁻¹) 1:= Costs.scalar ⟨ ε⁻¹, inv_pos.mpr he, 0,fun i p hv=> by simp only [ Pi.one_apply,pow_zero,mul_one,norm_inv]; gcongr; exact hp i ⟩
       rw [ show waveInt U μ f =(fun i p=> (1-V i)⁻¹ * waveInt U μ Z i p) from funext (fun i=>funext fun p=> by unfold Z; rw [ ← windCost hU H hx hV h hc hh]; field_simp [(norm_pos_iff.mp (lt_of_lt_of_le he (hp i)))]) ]; -- remove dummy
       convert (Costs.mul hz (ih hZ)) using 1; ext; simp; rw [pow_succ]; ring -- auto flatF eq
end YM.MS.Osc
