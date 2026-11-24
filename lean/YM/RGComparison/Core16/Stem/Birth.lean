import YM.RGComparison.Core16.Stem.Price
import YM.RGComparison.Core16.Normalize
/-!
# Whole-region price at all finite fixed regulator. Link-back guarantee

Supports physical moments read at this normalized scale. No assertion superuniform frame without
bringing the previous purchases. AFTER fixing all geometry/cutoff this algebra also makes
quantitative weak-coupling test possible before chunk purchases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Fk
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side} {ι k L T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D][Fintype L]
variable {X:Shelf G A D} {P: Planet X S ι k T} {Z:ChartRatio G}
local notation "Δ"=> Module.finrank ℝ (Panel G ι)
local notation "μ"=> Chart.tangent G ι
local notation "λ#"=> skillet G ι

lemma adieu : Tendsto (fun s:ℝ=>-Real.log s) Tested.germ atTop:= tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
lemma tollLess {p:ℝ→Prop}(h:∀ᶠ s:ℝ in atTop,p (dollar s)) : ∀ᶠ g in Tested.germ,p g:=by
    filter_upwards [adieu.eventually h,Tested.eventually_pos] with g he hh
    exact (show dollar (-Real.log g)= g by rw [dollar,neg_neg, Real.exp_log hh]) ▸ he
variable (H:P.Steady)(hZ: LocalRatio Z)
variable {p: Stuff G ι L}{ψ:(L→G.Color)→ℝ}{f:Melody G ι}{N:ℕ}{C:ℝ}(hF:Visible X ψ f p N C)
include H hZ hF
omit [Fintype L] in
theorem stella (j:ℕ){r:ℝ}(h1:0<r)(h2:r ≤ Chart.small G Z): Bill j (phaseAmt P (Chart.chamber G ι r)ᶜ f):=by
    let W:= (Chart.chamber G ι r)ᶜ; let y:= (Fintype.card ι:ℝ)
    have hW: MeasurableSet W:= (Chart.Ratio.chamber_open (U:=ι) hZ h2).isClosed_compl.measurableSet
    obtain ⟨b,hb,h⟩:= Descent.wall_bound Z h1 h2
    have hy:0≤y:= by unfold y; positivity
    refine ⟨(Real.exp (-1)*y)*|C|,by positivity,tollLess ?_⟩; filter_upwards [Error.residents X (G:=G),ruin_below (j+Δ),fare_falls.eventually (gt_mem_nhds hb),willing H.prices] with s he hz hr hh
    let g:=dollar s; have hg:0<g:=dollar_pos _; let U:=P.bureau g; let P₁:= {x:Sky G ι| crisp (fare s) Finset.univ x}; let D₁:= Δ
    have HA : W ⊆ P₁ᶜ:=by
       intro x hx hx'; apply hx; intro i _; by_contra hu; exact (not_lt_of_ge (h (x i) hu)) ((hx' i (Finset.mem_univ _)).trans hr)
    have hp : ∀ i,0≤ U i:=fun i=> (bureau_pos H hh i).le
    have hs: (∫ x in W,U x∂λ#) ≤ y*g^(j+D₁):=by
        have hce:=he S ι k T _ _ _ P H hh Finset.univ
        have hA : P.pot g ≤ 1:=by
            refine (integral_mono ((bureau_env H hh).integrable λ#) (integrable_const _) (fun x=> Base.output_le (H.tickets g hh) x)).trans_eq ?_; simp
        have hx : (∫ x in W,U x∂ λ#) ≤ (∫ x in P₁ᶜ,U x∂ λ#) := setIntegral_mono_set ((bureau_env H hh).integrable λ#).integrableOn (Eventually.of_forall hp) (Eventually.of_forall (fun i hi=> HA hi))
        apply (hx.trans hce).trans; rw [Finset.card_univ]; exact (mul_le_of_le_one_right (show 0≤ y * ruin s from mul_nonneg hy (Real.exp_pos _).le) hA).trans (mul_le_mul_of_nonneg_left hz hy)
    have hx: ‖∫ x in W,U x*f g x∂λ#‖ ≤ |C| *(y*g^(j+D₁)):=by
        refine (norm_integral_le_of_norm_le (g:=fun x=>|C| *U x) (((bureau_env H hh).integrable _).integrableOn.const_mul _) ?_).trans ?_
        · filter_upwards with x; rw [norm_mul, Real.norm_of_nonneg (hp x),Real.norm_eq_abs]; exact (mul_comm ..|>.le).trans (mul_le_mul_of_nonneg_right ((hF.price g hh x).trans (le_abs_self _)) (hp _))
        rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg C)
    change ‖phaseAmt P W f g‖ ≤ _; rw [phaseAmt,norm_mul,norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (g^Δ)⁻¹)]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by positivity)) (Real.exp_pos _).le).trans_eq ?_; change _* ((g^D₁)⁻¹ * (|C| *(y*g^(j+D₁))))= _*_ * g^j; rw [pow_add]; field_simp

omit H hF in
lemma cap_hot (p:Stuff G ι L)(hp:ContDiffAt ℝ ω ψ 0): ContDiffAt ℝ ω (cap Z p ψ) 0:= by
    have he:ContDiffAt ℝ ω (scene p) 0:=by apply contDiffAt_pi.mpr; intro j; unfold scene; rcases he:p j with i|i; exact turn_hot.contDiffAt.comp (f:=fun x:Door G ι=> x.2 i) _ ((contDiff_apply ℝ _ _).contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd); exact contDiffAt_fst.smul contDiffAt_const
    have hy: scene p (0:Door G ι)=0:=by funext j; unfold scene; cases p j <;> simp [spread,comp_apply]
    exact ((Chart.Ratio.jacobian_smooth hZ).comp (f:=Prod.snd) (0:Door G ι) contDiffAt_snd).mul ((hy.symm ▸ hp : ContDiffAt ℝ ω ψ (scene p (0:Door G ι))).comp _ he)
set_option maxHeartbeats 500000
lemma aspirant (hy:ContDiffAt ℝ ω ψ 0): Aspiration (phaseAmt P univ f) (harvest P Z p ψ):= by
    intro n
    obtain ⟨d,hd,hK,he⟩:= gate H hZ hF
    obtain ⟨r,hR,hr⟩:= Therm.aspirates μ _ _ n 1 (Fk.sturdy H) (Fk.bump_hot H) (cap_hot hZ p hy) (prepared H)
    let a:= min r d/2; let s:= harvest P Z p ψ; let W:= Chart.chamber G ι a; have ha:0<a := half_pos (lt_min hR hd)
    have hv:a<min r d:= half_lt_self (lt_min hR hd); have hp : a<d:= hv.trans_le (min_le_right ..)
    obtain ⟨u,hu,hU⟩:= stella H hZ hF (n+1) ha (hp.trans_le hK|>.le)
    obtain ⟨C,hC,h⟩:= hr a ⟨ha,hv.trans_le (min_le_left ..)⟩
    refine ⟨C+u,by positivity,?_⟩; filter_upwards [h,hU,tollLess (willing H.prices),Tested.eventually_pos] with g hg hw hh ht
    have hA : phaseAmt P univ f g= phaseAmt P W f g+ phaseAmt P Wᶜ f g:=by
        unfold phaseAmt; rw [← mul_add,← mul_add, integral_add_compl ((Chart.Ratio.chamber_open (U:=ι) hZ (hp.trans_le hK|>.le)).measurableSet) (regularize H hh (hF.env _ hh)), setIntegral_univ]
    change ‖phaseAmt P univ f g-peval s n g‖ ≤ _; rw [hA,add_sub_right_comm, he a ⟨ha,hp⟩ g ht hh]; exact (norm_add_le ..).trans ((add_le_add hg hw).trans_eq (add_mul ..).symm)
end YM.RGComparison.Core16.Lumen.Fk
