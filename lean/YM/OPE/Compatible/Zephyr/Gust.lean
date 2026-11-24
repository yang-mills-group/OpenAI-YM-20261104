import YM.OPE.Compatible.Zephyr.Zone
import YM.Next.RANK.Haar
import YM.PertExtension.BareChart
import YM.OPE.Compatible.Arch.Vuln
import YM.OPE.Compatible.Rail.Filly
/-! # Haar stencil radii don't depend on count. snap budget through2 -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric
variable {G:Gauge}{F:Type}{n:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
structure Sweep (N: ChartRatio G) (r R:ℝ): Prop where
    small : r < Chart.small G N
    sizes : 0<r ∧ 0<R
    acts : G.shell R ⊆ G.lieExp '' ball 0 r
    price (x:G.Color): x∈ ball 0 r → ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ G.chord (G.lieExp x) ≤ 2*‖x‖
variable {N:ChartRatio G}(hN: LocalRatio N){r t R B:ℝ}
include hN in
lemma request {p: G.Color→ Prop}(hp:∀ᶠ x in 𝓝 0,p x):∃ r R:ℝ, Sweep N r R ∧ ∀ x:G.Color,x∈ ball 0 r → p x:=by
       obtain ⟨s,hH,h⟩:= Metric.mem_nhds_iff.mp ((Next.Rank.metric_law G).and hp)
       let b:=min s (Chart.small G N/2); have hs:0<b:=lt_min hH (half_pos (Chart.Ratio.small_pos hN)); have hg:b< Chart.small G N:=(min_le_right ..).trans_lt (half_lt_self (Chart.Ratio.small_pos hN)); have ht : ball (0:G.Color) b⊆ ball 0 s:= ball_subset_ball (min_le_left ..); obtain ⟨R,hR,hr⟩:=Next.Rank.surrounds G (G.lieExp '' ball 0 b) (((LocalH.geom_patch G).choose_spec.2 b (hg.le.trans (min_le_right ..))).1.mem_nhds (show (1:G.El)∈ _ from ⟨0,mem_ball_self hs,G.mat_lieExp_zero⟩))
       exact ⟨b,R,⟨hg,⟨hs,hR⟩,hr,fun i hi=>(h (ht hi)).1⟩,fun i hi=>(h (ht hi)).2⟩
section
variable [Fintype F](G F)
abbrev Chamber B:= {p:Tile G F|∀ i, G.chord (p i) ≤ B}
abbrev CapeQ (B t r:ℝ) :Set (Keys G F):= {x|t•x∈ mounted (Chamber G F B) r}
variable {G F}
lemma era (h:Sweep N r R)(hv:0<t)(hx:0<B)(hg:B/2 ≤ r) : ball (0:Keys G F) (B/(2*t))⊆ CapeQ G F B t r ∧ CapeQ G F B t r ⊆ closedBall 0 (2*B/t):=by
    constructor
    · intro x hh; have he : t*‖x‖ < B/2:=by rw [mem_ball,dist_zero_right,show B/(2*t)=B/2/t by ring,lt_div_iff₀ hv,mul_comm] at hh; exact hh
      have hA:t•x∈ ball 0 r:= (show _ from by rw [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hv.le]; exact he.trans_le hg)
      refine ⟨fun i=> ?_,hA⟩; apply ((h.price ((t•x) i) (by rw [ball_pi _ h.sizes.1] at hA;exact hA i (mem_univ _))).2).trans; have hp : ‖(t • x) i‖ ≤ t*‖x‖:=(norm_le_pi_norm _ i).trans_eq (by rw [norm_smul,Real.norm_of_nonneg hv.le]); linarith
    intro x he
    obtain ⟨hy,hz⟩:=he; have hx : t*‖x‖≤2*B:=by
        rw [show t*‖x‖=‖t • x‖ from by rw [norm_smul,Real.norm_of_nonneg hv.le]]; refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hx.le)).2 (fun i=>?_); have hv':G.chord (G.lieExp ((t • x) i))≤ B:= (show ∀ i: F,G.chord _ ≤ B from hy) i; have ht:‖(t • x) i‖/2 ≤ G.chord (G.lieExp ((t • x) i)):=(h.price _ (by rw [ball_pi _ h.sizes.1] at hz; exact hz i (mem_univ _))).1; linarith only[ht,hv']
    rw[mem_closedBall,dist_zero_right,le_div_iff₀ hv,mul_comm]; exact hx
lemma chamberMeas : MeasurableSet (Chamber G F B):=by
      unfold Chamber; rw [setOf_forall]; refine MeasurableSet.iInter (fun i=>?_); exact measurableSet_le (G.continuous_chord.measurable.comp (measurable_pi_apply i)) measurable_const
lemma capeMeas :MeasurableSet (CapeQ G F B t r):= ((putC.measurable chamberMeas).inter isOpen_ball.measurableSet).preimage (show Measurable (fun x:Keys G F=> t • x) by fun_prop)
variable (h: Sweep N r R)
local notation "Pμ"=> Chart.physical G F
local notation "Tμ"=> Chart.tangent G F
local notation "Z"=> Module.finrank ℝ (Keys G F)
include hN h
lemma giving (p:Tile G F→ℝ)(hp:Measurable p)(hf:∀ x,x∉ Chamber G F B→ p x=0)(hr:B ≤ R)(ht:0<t):
    ∫ x,p x ∂ Pμ=t^Z * ∫ x in CapeQ G F B t r, Chart.jacobian N (t • x) * p (put (t • x)) ∂Tμ:=by
         let D:=Chart.chamber G F r; have he:Chamber G F B⊆D:=fun x hx i _=> h.acts ((hx i).trans hr)
         let A:=ball (0:Keys G F) r
         let E:= CapeQ G F B t r
         have hE : MeasurableSet E:=capeMeas
         let L(y:Keys G F):= Chart.jacobian N y * p (put y)
         let K:= A.indicator L
         have hS: (∫ x,p x ∂Pμ)=∫ x,K x ∂Tμ:=by
             have he':D.indicator p=p:=funext (fun i=>by by_cases h:i∈D; exact indicator_of_mem h _; rw [indicator_of_notMem h, hf _ (fun H=>h (he H))])
             rw [show (∫ x,K x ∂Tμ)=(∫ x in D,p x ∂Pμ) from (integral_indicator isOpen_ball.measurableSet).trans (Chart.Ratio.chamber_integral hN _ hp h.small h.sizes.1).symm, ← integral_indicator (Chart.Ratio.chamber_open hN h.small.le).measurableSet,he']
         have hz: K ∘ (fun x=> t • x)= E.indicator (fun x=> L (t • x)) := by
             funext x; by_cases hx:x∈E
             · change A.indicator _ _=_; rw [indicator_of_mem hx, indicator_of_mem (show t • x∈A from hx.2)]
             rw [indicator_of_notMem hx]; change A.indicator _ _=_; by_cases hv:t • x∈A
             · rw [indicator_of_mem hv]; unfold L; rw [hf _ (fun he=>hx ⟨he,hv⟩),mul_zero]
             exact indicator_of_notMem hv _
         have hσ := Measure.integral_comp_smul_of_nonneg Tμ K t (hR:=ht.le)
         rw [← integral_indicator hE]; rw [hS]; change _=t^Z*∫ x,(E.indicator (fun x=> L (t • x))) x ∂Tμ; rw [←hz,show (∫ x,(K ∘_) x ∂ Tμ)=_ from hσ]; change _=t^Z*((t^Z)⁻¹*_); field_simp
-- tax log d
abbrev feeX (N:ChartRatio G)(x:Keys G F):= ∑ i:F,rake N (x i)
lemma pay (x:Keys G F) (he:x∈ball 0 r) : Chart.jacobian N x=N.scale^(Fintype.card F)*Real.exp (feeX N x):=by
          have hp (i:F): 0< N.J (x i):= hN.pos (x i) (ball_subset_ball ((h.small.le.trans (min_le_left ..)).trans (half_le_self hN.patch.le)) (show x i∈ ball 0 r from by rw [ball_pi _ h.sizes.1] at he; exact he i (mem_univ _)))
          have hz(i:F): Chart.fee N (x i)= N.scale * Real.exp (rake N (x i)) := by rw [show Real.exp (rake N (x i))=_ from Real.exp_log (hp i)]; unfold Chart.fee; exact max_eq_left (mul_nonneg hN.scale.le (hp i).le)
          unfold Chart.jacobian feeX; simp_rw [hz]; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Real.exp_sum] -- verify
end
end YM.OPE.Zeph
