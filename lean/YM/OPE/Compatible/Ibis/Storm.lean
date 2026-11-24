import YM.OPE.Compatible.Ibis.Cou
/-! # Low touch forecast from physical witnesses at given size. no orientation restrictions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d t:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
section
variable (V:Train i)(h:4 ≤ i)
abbrev ViewsK (h:4 ≤ i)(K:KernelChoices)(j:ℕ):=∑ d∈range (j+1),‖Fortune (UpΩ K i h+1) d 0 2‖
noncomputable abbrev σGm (h:4 ≤ i)(G:Gauge)(K:KernelChoices)(m k:ℕ):= (bootPrice (Shade G) m k (1/2) (A:=(terra_money K h).choose+1) (show 0≤_ from add_nonneg (terra_money K h|>.choose_spec.1) zero_le_one)).choose -- named A
noncomputable abbrev SearZ (G:Gauge)(k m d b:ℕ)(R U W r ε B:ℝ):= ‖Cap (Shade G) d k m‖*(W*R + ε*B)+GramU G b m k*(W*R +r *U)
lemma LowQ (x:Site n)(p:Seat k m (Shade G))(hp:settled (m:=m) p)(ht:Volume (lilies m k _ p) k (m+t) R)(hv:0≤r)(hh:2*(b+1)<n.val)(he:0≤ε)(hl:d≤ j+1)
        (hS: Spectre (Vessel K V G n h) (Chart.tangent G (Body 1 n)) (LightP x (m:=m) p) j r)
        (hA:∀ q∈ Hoard G b k m, ‖boostS (rentV G V h K n) (1/2) m k q-boostS (atlasF G V h K) (1/2) m k q‖≤ ε*‖q‖) :
       ‖Cap (Shade G) d k m (boostS (atlasF G V h K) (1/2) m k p)‖ ≤ SearZ G k m d b ((Wfee_Z t b)⁻¹*R) (ViewsK h K j) (σGm h G K m k) r ε R:=by
             obtain ⟨P,hP,H,E⟩:= safeC p b ht; let θ:= (1/2:ℝ); let V':= atlasF G V h K; let A:= rentV G V h K n; let f:= boostS V' θ m k; let g:= boostS A θ m k; let B:=g P; let U:=σGm h G K m k; let W:= (Wfee_Z t b)⁻¹*R; let L:= Cap (Shade G) d k m
             let s:=(terra_money K h).choose+1; have hs:0 ≤ s:=A.positive; obtain ⟨hU,hK⟩:= (bootPrice (Shade G) m k θ hs).choose_spec; have hU:0≤ U:= hU
             have hf : ‖f p-B‖≤ U*W+ε*R:=by
                  apply (norm_sub_le_norm_sub_add_norm_sub (f p) (f P) B).trans; rw [←map_sub,norm_sub_rev (f P) B]; exact add_le_add ((hK V' (le_add_of_nonneg_right (show (0:ℝ)≤ 1 by norm_num)) _).trans (mul_le_mul_of_nonneg_left E hU)) ((hA P hP).trans (mul_le_mul_of_nonneg_left H he))
             let T:= ViewsK h K j; rw [show L (f p)= L (f p-B)+L B from (by rw[map_sub]; abel)]
             refine (norm_add_le ..).trans (add_le_add ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _))) (gumSafe x B hh (delve P hP A θ) (R:=U*W+r*T) ?_ ?_))
             · intro i hi z; let u(i:Fin i):deck (Shade G) n:= Pi.single (z i) (1:ℝ) -- explicit
               let Q(x'):=(cashRead (k:=k) (m:=m) x i u) x'; have hv' : ‖Q B-Q (g p)‖ ≤ U*W:=by
                    rw [show Q B-Q (g p)=Q (B-g p) from (map_sub ..).symm,show Q _= _ from stamp_C x (k:=k) (m:=m) (B-g p) u]; apply (price_H (k:=k) (m:=m) x _ z).trans ; change ‖g P-g p‖≤ _; rw [norm_sub_rev, ←map_sub]; exact (hK A le_rfl (p-P)).trans (mul_le_mul_of_nonneg_left E hU)
               let Ω:= scribe x (lilies m k _ (g p) i) u; have hQ : Q (g p)=Ω:= stamp_C x ..; have hG : ‖Q (g p)‖ ≤ r*T:= hQ ▸ (show ‖Ω‖ ≤ r*T from (spotlight V h x p hp z (hS.bound (by omega:i ≤ j))).trans (mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans (Finset.single_le_sum (f:=fun n=>‖Fortune (UpΩ K _ h+1) n 0 2‖) (fun _ _=>norm_nonneg _) (mem_range.mpr (by omega)))) hv))
               rw [← stamp_C x B]; exact (show ‖Q B‖≤ _ by nth_rw 1 [←(sub_add_cancel (Q B) (Q (g p)))]; exact (norm_add_le ..).trans (add_le_add hv' hG))
             exact add_nonneg (mul_nonneg hU ((norm_nonneg _).trans E)) (mul_nonneg hv (sum_nonneg fun _ _=> norm_nonneg _))
end
end YM.OPE.Ibis
