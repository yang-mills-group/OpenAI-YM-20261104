import YM.OPE.Compatible.Gems.Steal
/-! # Treasury locality.Root stencil worth -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m j:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
open Module
variable {K:Sponsor G}{T:Seasons K}
section
-- general Keys cost sum
variable {I E:Type} [MeasurableSpace E]{M:Measure E}[IsProbabilityMeasure M]
open Lav
abbrev J1 :price := fun _=>1
lemma powerQ {p:E→ℝ}{C:price}(h:Cane M p C)(i:ℕ): Cane M (p^i) (hikeP C i):=by
       induction i with
       | zero=> rw[pow_zero]; exact Cane.constant _ (show ‖(1:ℝ)‖ ≤ 1 by norm_num)
       | succ i ih=> rw[pow_succ']; exact h.mul ih
omit [IsProbabilityMeasure M] in lemma of_K {Y X:Type}[NormedAddCommGroup Y][NormedAddCommGroup X]{p:E→X}{q:E→Y}{C:price}(h:Cane M p C)(hp:AEStronglyMeasurable q M)(he:∀ x:E,‖q x‖≤ ‖p x‖): Cane M q C:= fun _ hi=> (h _ hi).ofLe hp (Eventually.of_forall he) -- unused
variable [Fintype I]
noncomputable abbrev Hue (u:E→Libra.Keys G I)(i:I×G.ColorIndex)(x:E):= castAt (Limn.Tip G I) i (u x)
omit [MeasurableSpace E][IsProbabilityMeasure M] in lemma BitGl (x:Libra.Keys G I): ‖x‖ ≤∑ i:I×G.ColorIndex,‖castAt (Limn.Tip G I) i x‖:=by
       let Q:=Limn.Tip G I; nth_rw 1 [←Q.sum_repr x]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [norm_smul]; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) le_rfl; rw [show Q i= Pi.single i.1 (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) from (by unfold Q Limn.Tip; rw [Basis.reindex_apply,Pi.basis_apply];rfl)]; refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=>?_ ; by_cases h:j=i.1
       · subst j; rw [Pi.single_eq_same,OrthonormalBasis.norm_eq_one]
       rw [Pi.single_eq_of_ne h,norm_zero]; exact zero_le_one
noncomputable abbrev hueCost (C:price)(n:ℝ)(G:Gauge): price:= fun i=> (n*(Fintype.card G.ColorIndex:ℝ))* C i
lemma hueEarn (u:E→Libra.Keys G I)(p:price)(hp:(Fintype.card I:ℝ)≤ s)(hz:∀ i:ℕ,0 < i→ 0 ≤ p i)(he:AEStronglyMeasurable u M)(hf:∀ i:I×G.ColorIndex, Cane M (Hue u i) p) : Cane M u (hueCost p s G):=by
       have hh:= Cane.sum Finset.univ (fun i x=> ‖Hue u i x‖) (fun _=>p) (fun i _=> Cane.normVal (hf i)); apply (of_K hh he _).grow; swap
       · intro x; rw[Finset.sum_apply]; exact (BitGl _).trans (Real.le_norm_self _)
       intro j hj; rw [Finset.sum_apply]; unfold hueCost; simp only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (hz j hj)
end
section Host
variable (L:Host K T)(Y:Studio L)
local notation "Fθ"=> L.ForestQ
noncomputable abbrev Hσ (X:Seats Fθ)(x:Y.St):= rip L.Z L.H G X (Vtone L Y x)
lemma HN (X:Seats Fθ)(i:Rubric G X)(x:Y.St): Hue (Hσ L Y X) i x=PulseP L Y (Sum.inr (shout G X i)) x:=by rw [PulseP,breezeY,Tip_ψ]; change cash (Limn.Tip G (↥X)) (Hσ L Y X x) i= _; rw[Tip_ψ];rfl -- full repr
lemma HσC (X:Seats Fθ): Continuous (Hσ L Y X):= (rip L.Z L.H G X).continuous.comp (continuous_const.add ((stake Y.X).continuous.comp (continuous_id.add continuous_const))) -- infer
variable {L Y}
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv: Scale Y t)
include h ht hc he hv
lemma Crew (X: Seats Fθ)(hx:(X.card:ℝ)≤z): Cane Y.μφ (Hσ L Y X) (hueCost (FWind G s c u C t) z G):=by
       refine hueEarn (Hσ L Y X) _ (by rwa [Fintype.card_coe]) ?_ (Continuous.aestronglyMeasurable (HσC ..)) (fun i=>?_)
       · intro i hi; unfold FWind; have ht:0 ≤ t:=(norm_nonneg _).trans hv.w; have hp:0≤ Pξ G s c u C t:= (norm_nonneg _).trans (stareT h (by assumption) hc he hv); exact add_nonneg (add_nonneg ht hp) (mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left ..)))
       rw [funext (HN L Y X i)];exact TinV h ht hc he hv _ -- binder names
noncomputable abbrev RiseT (G:Gauge)(k:ℕ)(s c u C t z a:ℝ):price:=‖a‖ • hikeP (J1+hueCost (FWind G s c u C t) z G) k
lemma Fans (X:Seats Fθ)(hx:(X.card:ℝ)≤ z)(q:Sender L)(hp:Funded L X q a k)(i:Phase): Cane Y.μφ (fun x=> (q (Vtone L Y x)).seq i.val) (RiseT G k s c u C t z a):=by
        obtain ⟨y,hy,hq⟩:=hp.net; let f:= fun x=>‖Hσ L Y X x‖; let v:=1+f; have ht:= (Crew h ht hc he hv X hx); have hp:=powerQ ((Cane.constant (μ:=Y.μφ) 1 (show ‖(1:ℝ)‖≤ 1 by norm_num)).add ht.normVal) k; rw [hq]; apply of_K (hp.scal a); · exact ((hy.spikes i).comp (HσC ..)).aestronglyMeasurable
        intro x; exact (hy.earn (norm_nonneg _) _ le_rfl i).trans (Real.le_norm_self _)
end Host
end YM.OPE.Borealis.Galea
