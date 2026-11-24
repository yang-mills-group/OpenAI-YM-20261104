import YM.RG12.Orifice.Drop
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Palmate
import YM.RG12.Spins.Tubal
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Orifice.CashCond
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Gate Scroll Vine Tablet Metric Pulse Itinerary
variable {x Y W η r Q:ℝ} {n j:ℕ}
-- simpler: analytic.Ray full Gauge rotation.P.Content only when seeds empty.Body. no uniform coerc claim.
def film (X : Coat T F)(i:Bond f)(V:Config G c):= (vary X V).condensation i
open Source WardBin.Lies Set
section lane
variable (X : Coat T F) (hd:X.seeds=(blank X).seeds)(hM:X.x=x)(hi:X.width=W)
-- x> via temperature.P
lemma pose (c : Side)(n:ℕ): ∃ C:ℝ, Mode (increment (1:Config G c)) (0:Directions G c) n C:=by
   obtain ⟨K,-,hk⟩:=expCost G n 1
   refine ⟨_,fromLogL id (linearB (ContinuousLinearMap.id ℝ _) (by change ‖(0:Directions G c)‖≤(1:ℝ); simp) (one_mul (1:ℝ)|>.symm ▸ ContinuousLinearMap.norm_id_le) zero_le_one) 1 zero_lt_one hk (by intro j; simp) 1⟩
include hd hM hi
lemma flat (hR:Tent P L x W η r Q Y T)(ht:0<Pressure.temp x)(i:Bond f)(z:Site c→G.El) : ∀ᶠ V : Config G c in 𝓝 1, film X i V= film X i (gauge z V):=by
   filter_upwards [ProjectorNext.Equivariance.offFlags (G:=G) (Pressure.temp x) ht] with V hv
   set V':= vary X V; have hm: V'.manifest := by
      unfold Coat.manifest V'; change X.seeds.flags=flags (Pressure.temp X.x) V; rw [hd,hM,hv];rfl
   obtain ⟨hs,hp,hL,_⟩:= hR F V' hM hi hm
   have h:= V'.rotation_at z hs (hL z) i
   change (V').condensation _ = _; unfold Coat.condensation; rw [← h]; rfl
lemma still (hG:G.Simple)(hR:Tent P L x W η r Q Y T)(ht:0<Pressure.temp x)(i:Bond f)(he:DifferentiableAt ℝ (film X i ∘ increment (1:Config G c)) 0): fderiv ℝ (film X i ∘ increment (1:Config G c)) 0=0:=by
   apply ContinuousLinearMap.ext; intro v
   refine Stationary.slot_fixed hG _ (fun u p=> ?_) v
   let A:= AnalyticBridge.VerifiedReset.colorMove (n:=c) u
   apply Stationary.chain_fixed (F:=film X i ∘ increment _) A _ he p
   have ht' : Tendsto (increment (1:Config G c)) (𝓝 0) (𝓝 1):=by
       have hm:Continuous (increment (1:Config G c)):=by unfold increment; fun_prop
       simpa only [Work.G07.at_zero_increment] using! hm.tendsto (0:Directions G c)
   filter_upwards [ht'.eventually (flat X hd hM hi hR ht i (fun _=>u))] with V hv
   simp only [Function.comp_apply,A,AnalyticBridge.VerifiedReset.exp_move]; exact hv.symm -- exp_move API
-- convert Mode.Spark identity paths to algebra-slope to purchase D¹ zero.Suitable at PHYS origin.For Hig.Tube argument tests.
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U:E→ Config G c}{p:E}{s:ℝ}
lemma route0 (hG:G.Simple)(hR:Tent P L x W η r Q Y T)(ht:0<Pressure.temp x)(i:Bond f)(he:DifferentiableAt ℝ (film X i ∘ increment (1:Config G c)) 0)
   (hm:Mode U p n s)(hn:1≤n)(hs:U p=1) : film X i (U p)=0 ∧ fderiv ℝ (fun t=>film X i (U t)) p=0:=by
   constructor
   · rw [hs]; unfold film Coat.condensation; have h:Coat.blank (vary X (1:Config G c))=(vary X 1):=by
       unfold Coat.blank; obtain ⟨hx,hy,hL,hD,hQ,hY,hB⟩:= X; simp only [vary] at *; unfold Coat.blank at *; -- ar fields
       grind
     rw [h,sub_self,zero_div]
   let f t (i : Edge (Site c)):= G.plog (G.mat (U t i))
   have hf(i : Edge (Site c)): DifferentiableAt ℝ (fun t=>G.mat (U t i)) p:= ((hm.atLink i).smaller hn).smooth.differentiableAt (by simp)
   have hV i: U p i=(1:G.El):=by rw [hs];rfl
   have ht':f p=(0:Directions G c):=by funext i; unfold f; rw [hV i,G.mat_one,G.plog_one];rfl
   have hh : DifferentiableAt ℝ f p:= differentiableAt_pi.mpr fun i=> DifferentiableAt.comp (f:=fun t=>G.mat (U t i)) p (show DifferentiableAt ℝ G.plog (G.mat (U p i)) by rw [hV,G.mat_one]; exact G.plog_diff.differentiableAt (by simp)) (hf i) -- comp param names?
   have heq : ∀ᶠ t in 𝓝 p,U t=increment (1:Config G c) (f t) :=by
      suffices hv:∀ i,∀ᶠ t in 𝓝 p,U t i=increment 1 (f t) i from ((eventually_all.mpr hv).mono (fun t h=>funext h))
      intro i
      have hg : Tendsto (fun t=> U t i) (𝓝 p) (𝓝 (1:G.El)):=by
        apply (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
        simpa only [Function.comp_def,hV] using! (hf i).continuousAt.tendsto
      filter_upwards [hg.eventually G.plog_right] with t hz
      unfold increment f; change _=G.lieExp _ *1; rwa [mul_one,eq_comm]
   have hZ := still X hd hM hi hG hR ht i he
   change fderiv ℝ (film X i ∘ U) p=_; rw [(((show U=ᶠ[𝓝 p] (increment (1:Config G c) ∘ f) from heq).fun_comp (film X i)):film X i ∘ U =ᶠ[𝓝 p] (film X i ∘ increment 1)∘ f).fderiv_eq]; change fderiv ℝ ((film X i ∘ increment 1) ∘ f) p = _; rw [fderiv_comp (g:=film X i ∘ increment 1) p (show DifferentiableAt ℝ (film X i ∘ increment 1) (f p) by rw [ht']; exact he) hh,ht',hZ]; simp
end lane
end YM.RG12.Orifice.CashCond
