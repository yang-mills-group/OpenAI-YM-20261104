import YM.AllOrder.Laplace.Native
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Afresh
/-! # Shift cumulants at horizontal input; needed for exact low cancellation.
Moment proof uses integrable lens ratio over all z, not a stationarity-of-true measure hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical MatrixOrder
open Matrix Finset Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern Local Vote PositionX.Jet Shield Progress.StationaryScenes Green
open scoped BigOperators Matrix.Norms.Frobenius
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
local notation "Ω"=> ℝ × X
variable {A B:X×Poll.Body ι→ℝ}{ρ:X→Poll.Body ι}{M:X→Matrix ι ι ℝ}(h:Accent A B M ρ)
local notation "K"=>M 0
local notation "μ"=>sweep (M 0)⁻¹
variable (hb:∀ i j, ContDiffAt ℝ ω (fun x=>M x i j) 0) {c b:ℝ} (he:∀ z:ι→ℝ,dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z)(hc:Bottom (M 0) b)(hp:0<b)
include h he
lemma raw_live (k:ℕ): Integrable (Vote.probe A B ρ M k) (sweep (M 0)⁻¹) := by
 obtain ⟨u,w,p,ha⟩:= hollow h k; obtain ⟨C,-,hE⟩:= Brush.compact (k:=k) isCompact_Icc (f:=Real.exp) (s:=Icc 0 2) fun i _=> Real.contDiff_exp.contDiffAt
 exact (raw_h ha le_rfl he (p:=p) (k:=k) (show _ ≤ (Fintype.card ι:ℝ) from le_rfl) (hE 0 (by norm_num)) le_rfl).1
open GaussianFourier
lemma even_c (k:ℕ)(x:X)(r:ℝ): Tensor.diagonal (Vote.moment A B ρ M k) (r,x)= Tensor.diagonal (Vote.moment A B ρ M k) (-r,x):= by
 let V y:= Real.exp ∘ grace A B ρ M y; let T:= Vote.probe A B ρ M k; let ξ:= ContinuousMultilinearMap.apply ℝ (fun _:Fin k=> Ω) ℝ (fun _=>(r,x)); let t':=(k.factorial:ℝ)⁻¹;
 let P z:= (ξ (T z)); let g z:= Tensor.diagonal (T z) (-r,x)
 have ht (z:Y): g (-z) = P z:= by
    let D₁:= -(ContinuousLinearMap.fst ℝ ℝ X); let D:= D₁.prod (ContinuousLinearMap.snd ℝ ℝ X); have hx (r':Ω): V (-z) (D r')= V z r':= congr_arg Real.exp (oppositeC ..)
    have hv:= (grace_nice h (-z) k).exp; let L:= V (-z); have hg:L ∘ D=V z:= funext hx
    change _ = iteratedFDeriv ℝ k (V z) 0 _; rw [←hg, Next.Foundations.jets_linear D (show ContDiffAt ℝ (↑k) L 0 from hv), ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
 unfold Vote.moment Vote.raw Tensor.diagonal; rw [_root_.smul_apply,_root_.smul_apply,ContinuousMultilinearMap.integral_apply (raw_live h he k),ContinuousMultilinearMap.integral_apply (raw_live h he k)]; change t'*(∫ z,P z ∂μ)=t'* ∫ z,g z ∂μ; apply congr_arg (t'*·)
 have hm : ((K)⁻¹).PosDef:= (h.station.self_of_nhds.1).inv; rw [recommends _ hm,recommends _ hm]; conv_rhs => rw [← integral_neg_eq_self (fun z:Y=> lens₀ (K)⁻¹ z*g z)]
 simp only [ht,symL]
include hb hp hc
abbrev plazzo (S : Matrix ι ι ℝ)(s: Matrix ι ι ℝ)(x:Body ι) := Shield.lens₀ s⁻¹ x/Shield.lens₀ S⁻¹ x
lemma barren (k:ℕ)(hk:k≠0) (x:X) : Tensor.diagonal (Vote.moment A B ρ M k) (0,x)=0:= by
 let F(x:X) (z:Poll.Body ι):= plazzo (M 0) (M x) z
 have hK:(M 0).PosDef:= h.station.self_of_nhds.1; have hx : IsUnit (M 0).det:= isUnit_iff_ne_zero.mpr hK.det_pos.ne'
 have heq : (M 0)⁻¹⁻¹=M 0:= Matrix.nonsing_inv_nonsing_inv _ hx
 obtain ⟨U,hU,hI,hG⟩:= Flux.winglet (A:=fun x=> (M x)⁻¹) (V:=fun (z:Y) (_:X)=>z) (Z:=id) hK.inv (heq.symm ▸ hc) hp (fun i j=> (jetBack hb hx i j).of_le (show ↑(k:ℕ)≤ω from le_top)) (by
     simp only [id_eq,sub_self]; exact Zest.still (0:Y))
 have hB : Meristem F 0 μ k:= (Meristem.points F _ ⟨U,hI,hG⟩ (Eventually.of_forall fun i=>Measurable.div (bulbB (fun _ _=> measurable_const) measurable_id) (bulbB (fun _ _=>measurable_const) measurable_id))).1
 have hv : (fun x=>∫ z,F x z ∂μ)=ᶠ[𝓝 0] fun _=>1:= by
    filter_upwards [h.station] with x hx
    rw [recommends _ hK.inv (F x)]; change (∫ z,_)=_; let f:= lens₀ (M x)⁻¹; rw [show (fun z:Y => lens₀ (M 0)⁻¹ z* F x z)= f from funext (fun z=> by unfold F plazzo; rw [mul_comm,div_mul_cancel₀ _ (fullFuel (M 0)⁻¹ z).ne'])] -- lemma proof type
    have hg:= recommends _ hx.1.inv (fun z=> (1:ℝ)); simpa [f] using hg.symm
 have hh(z:Y): (fun y=>F y z)=ᶠ[𝓝 0] (fun y:X=>Real.exp (grace A B ρ M z (0,y))) := by
   filter_upwards [h.station] with x hx; apply (div_eq_iff (fullFuel _ z).ne').mpr; rw [mul_comm]; apply Eq.symm (meter A B ρ M z (fun v hv=> ?_)); rcases Set.mem_insert_iff.mp hv with rfl|rfl -- rfl singleton is Mem not equality
   · have ht:=h.station.self_of_nhds; exact ⟨ht.1,fun z=>(ht.2 z).2⟩
   exact ⟨hx.1,fun z=>(hx.2 z).2⟩
 let Z z:= Tensor.diagonal (JetF F k 0 z) x; let T x:= ∫ z,F x z ∂μ
 have ht(Z'): Z Z'=Tensor.diagonal (Vote.probe A B ρ M k Z') (0,x):= by unfold Z Tensor.diagonal JetF; rw [((hh Z').iteratedFDeriv ℝ k).eq_of_nhds]; let L:=ContinuousLinearMap.inr ℝ ℝ X; change iteratedFDeriv ℝ k ((Real.exp∘ grace A B ρ M Z')∘ L) 0 _= _; rw [Next.Foundations.jets_linear L (show ContDiffAt ℝ (↑k) (Real.exp∘ _) _ from (grace_nice h Z' k).exp),ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
 have hδ : 0= ∫ z,Z z ∂μ := by
    have ht := (hB.calls.2 k (Nat.le_refl k)); rw [(hv.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne hk] at ht; unfold Z Tensor.diagonal; rw [← ContinuousMultilinearMap.integral_apply ht.1,← ht.2]; rfl
 rw [Vote.moment, Tensor.diagonal, _root_.smul_apply,Vote.raw,ContinuousMultilinearMap.integral_apply (raw_live h he k)]; change _ • (∫ z,Tensor.diagonal _ ((0:ℝ),x) ∂μ)=0; simp_rw [← ht]; rw [← hδ,smul_zero]
end YM.AllOrder.Laplace.SigmaP
