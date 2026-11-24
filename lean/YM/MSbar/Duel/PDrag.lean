import YM.MSbar.Duel.Reef
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
variable (F: View τ→ℝ)(T: View ι→L[ℝ] View τ)
variable (q:Pot σ)(x:View ι)(hf:Reef F 1)
local notation "ω'"=> fieldLaw D
local notation "Y"=>present A C'
noncomputable def faceA (q : Pot σ)(x:View ι)(y:View τ) := fderiv ℝ (fun x:View ι=> actor A C' F T q x y) x
noncomputable def drag (q:Pot σ)(x:View ι) := ∫ y,actor A C' F T q x y∂fieldLaw D
variable (b:ℝ)
local notation "j!"=> actor A C' F T
local notation "φ"=>faceA A C' F T
local notation "δ"=> fieldLaw D
include h hf
lemma Region (u:View ι)(hb:0≤b): ∃ v: View τ→ℝ, Integrable v δ∧∀ x:View ι, ‖x‖ ≤ b→ ∀ y:B, ‖(faceA A C' F T q x y u)‖ ≤ v y:=by
    let q':=dint (A*ᵥu) q; obtain ⟨P',hp⟩:=dim_cost A C' q b hb; obtain ⟨Q',hQ⟩:=dim_cost A C' q' b hb; obtain ⟨a,ha,hA⟩:= Lodge.meter hf.smooth hf.cost ([]: List B) (by simp); obtain ⟨b',hx,hh⟩:= Lodge.meter hf.smooth hf.cost [T u] (by simp); let g(w:Pot τ)(x:B):=MvPolynomial.eval x w
    have he(w:Pot τ): Integrable (g w) δ:=by let u:=((grille (1:Matrix τ τ ℝ) h w (0:B) 1 (by simp)).integrable le_rfl); simpa using u -- syntax
    let f(x:B):=g Q' x*a+g P' x*b'; refine ⟨f,(he _|>.mul_const a)|>.add ((he _).mul_const b'),fun x hx y=>?_⟩
    change |hPoke A C' F T q u x y| ≤ _; rw [peaks A C' F T q x hf u y]; unfold actor; refine (abs_add_le ..).trans (add_le_add (b:=g Q' y*a) ?_ ?_); all_goals rw [abs_mul]; apply mul_le_mul <;> first|exact (hQ y|>.2 _ hx)|exact (hp y|>.2 _ hx)|exact hA _|exact hh (y+T x)| exact hp y|>.1| exact hQ y|>.1| exact abs_nonneg _
lemma paidRegion : Integrable (faceA A C' F T q x) δ∧ HasFDerivAt (drag A C' D F T q) (∫ y:View τ,faceA A C' F T q x y∂δ) x:=by
    let K:= ‖x‖+1
    let C (y):=φ q y; have ht:Continuous (C x):=by
         let f(y:W×B):=actor A C' F T q y.1 y.2; have hu := (actorD A C' F T q hf).continuous_fderiv (by simp); let M:= (ContinuousLinearMap.id ℝ W).prod (0:W→L[ℝ] B); have he : C x= fun z=> (fderiv ℝ f (x,z)).comp M:=by
            funext z; let V₀(v:W):=(v,z); have hh: HasFDerivAt V₀ M x:= (hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const z x) -- signature
            exact (((actorD A C' F T q hf|>.differentiable (by simp) (x,z)).hasFDerivAt).comp x hh).fderiv
         rw [he]; exact (show Continuous (fderiv ℝ f) from hu).comp (continuous_const.prodMk continuous_id)|>.clm_comp continuous_const
    let G₃(u:W):= ‖u‖<K; have hk:0<K:= add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one; choose f hf he using fun i:ι=> Region A C' D h F T q hf K (bolt i) hk.le -- shadow
    let H₁(x:B):= ∑ i,f i x; have hH:Integrable H₁ δ:= integrable_finsetSum univ (fun i _=> hf i); have hX(x:W)(hx:‖x‖<K)(y:B) : ‖C x y‖ ≤ H₁ y:=by
         have hv(i):0≤ f i y:= (norm_nonneg _).trans (he i x hx.le y); refine ContinuousLinearMap.opNorm_le_bound _ (M:=H₁ y) (sum_nonneg fun i _=> hv i) ?_; intro v; nth_rw 1 [Lis.spiral v]; unfold H₁; rw [sum_mul,_root_.map_sum]; refine (norm_sum_le ..).trans (sum_le_sum (fun z _=>?_)); rw [_root_.map_smul,norm_smul,mul_comm]; exact mul_le_mul (he z x hx.le _) (norm_le_pi_norm v z) (norm_nonneg _) (hv z)
    have hq:‖x‖ < K:=lt_add_of_pos_right _ zero_lt_one; refine ⟨ hH.mono' ht.aestronglyMeasurable (Eventually.of_forall (hX _ hq)),?_⟩
    let q'(x): Integrable (actor A C' F T q x) δ:= fresh A C' D h F T q x ‹Reef ..›; refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=actor A C' F T q) (F':=C) (show {x: W | ‖x‖ < K}∈𝓝 x from continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds hq)) (Eventually.of_forall (fun x=>(q' x).aestronglyMeasurable)) (q' x) ht.aestronglyMeasurable (Eventually.of_forall fun a x h=> hX x h a) hH (Eventually.of_forall fun a p _=>?_)
    exact (((actorD A C' F T q ‹Reef F 1›).comp (f:=fun v:W=>(v,a)) (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p).hasFDerivAt
end YM.MSbar.Duel
