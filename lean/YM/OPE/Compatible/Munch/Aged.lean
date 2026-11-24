import YM.OPE.Compatible.Munch.Porch
/-! # GP bill full and boarded, sharp footprint powers. wider than refund. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f)
noncomputable def ung (x:Site L.f)(j:ℕ)(s:ℝ)(p:Site L.f)(z:RodZ L n):ℝ:= if p∈neighbors (16*j) x then burst s (Inrange L p z) else 0
noncomputable abbrev ticPay (p:Site L.f)(z:RodZ L n)(j:ℕ)(t:ℝ) := wigP x t p z+ ung x j t p z
lemma unt_J (p:Site L.f)(z:RodZ L n):0 ≤ ung x j t p z:=by unfold ung; split; exact Real.exp_nonneg _; exact le_rfl
lemma on_J (p:Site L.f)(z:RodZ L n)(h:Dtn x p≤ 16*(j:ℝ)): burst t (Inrange L p z) ≤ ticPay x p z j t:=by
     have hh:p∈neighbors (16*j) x:=(neighbors_mem ..).mpr (by exact_mod_cast h); unfold ticPay ung; rw [if_pos hh]; exact le_add_of_nonneg_left (wake ..)
noncomputable abbrev jigB (G:Gauge)(n j:ℕ)(t:ℝ):= tokenCost G n t+(ballCost (16*j):ℝ)*ΛGram G t ^n
lemma Jig (ht:0 < t)(n j:ℕ): ∑ p:Site L.f,∑ z:RodZ L n,ticPay (L:=L) x p z j t≤ jigB G n j t:=by
          unfold ticPay; simp_rw [sum_add_distrib]; apply add_le_add (κBudget x n ht); let S:= neighbors (16*j) x; rw [show ∑ p:Site L.f,∑ z:RodZ L n,ung x j t p z=∑ p∈S,∑ z:RodZ L n,ung x j t p z from (Finset.sum_subset (subset_univ S) (fun _ _ hx=>by unfold S at hx; simp [ung,hx])).symm]; apply (sum_le_sum (g:=fun _=>ΛGram G t ^n) (fun p hp=>?_)).trans; swap
          · unfold S at hp; simp_rw [ung,if_pos hp]; apply τgo; exact ht
          rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card (16*j) x) ((sum_nonneg (fun _ _=>Real.exp_nonneg _)).trans (τgo (L:=L) x n ht))
lemma Dugout (f:Site L.f→RodZ L n→ℝ)(h:∀ p z,‖f p z‖≤ a*ticPay x p z j t)(hv:0 ≤ a)(ht:0 < t): ‖∑ p,∑ z,f p z‖ ≤ a*jigB G n j t:=by
          apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_left (Jig x ht n j) hv); rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [Finset.mul_sum]; exact (norm_sum_le ..).trans (sum_le_sum fun _ _=>h ..)
lemma Norm_K {d f b Z W q:ℝ}(ht:0≤Z)(hs:0 < s)(hu:0 < u)(hq:0≤q)(hp:‖b‖ ≤ q* Real.exp (-(s*Z)))
          (h:D ≤2*d) (hd:0<d)(hx:‖f‖≤ W)(he: Z ≤ d/32→ ‖f‖≤W*Real.exp (-(u*(d/8)))) : ‖b*f‖ ≤ q*W*Real.exp (-Gov s u*(D+Z)):=by
              apply le_trans (Issue (D:=d) (t:=0) le_rfl hd.le h ht hs hu hq hp (show Pulses f d Z 0 W u from ⟨hx,fun hv _=> by linarith,fun _ h=> he h⟩)); rw [_root_.zero_add]
lemma swayPay {z b f:ℝ}(he:0≤z)(hs:0<s)(hu:0<u)(hq:0 ≤ A)(hp:‖b‖≤ A*Real.exp (-(s*z)))(hw:‖f‖ ≤ D): ‖b*f‖ ≤ A*D*burst (Gov s u) z:=by
              obtain ⟨h,h',_⟩:= Gov_price hs hu; have hh:0 ≤ D:= (norm_nonneg _).trans hw; rw [norm_mul,mul_right_comm A]; apply le_trans (mul_le_mul hp hw (norm_nonneg _) (mul_nonneg hq (Real.exp_nonneg _))); apply mul_le_mul_of_nonneg_right _ hh; apply mul_le_mul_of_nonneg_left _ hq; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_right h' he,mul_nonneg h.le he]
end
end YM.OPE.Borealis.Galea
