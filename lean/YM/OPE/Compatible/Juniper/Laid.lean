import YM.OPE.Compatible.Juniper.Patch
/-!
# quantitative BI.k_CPU. compact merit poland
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
local notation "Fλ"=> fieldX (Shade G)
section
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable {p:E→ℝ}(v:JetS E)
noncomputable def TagN (v:JetS E):ℝ:=1+ ‖v.s‖+ ‖v.l‖+‖v.h‖
omit [NormedSpace ℝ E] in
lemma VatR : 1 ≤ TagN v:=by unfold TagN; linarith only [norm_nonneg v.s,norm_nonneg v.l,norm_nonneg v.h]
lemma Spat (x:ℝ)(h:|x| ≤1): ‖v.atK x‖≤ TagN v:=by
      unfold JetS.atK TagN; have he(i:ℕ)(y:E): ‖x^i • y‖ ≤ ‖y‖:=by rw [norm_smul,norm_pow,Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) h)
      have hz:= (norm_add_le (v.s + x • v.l) (x^2 • v.h)).trans (add_le_add ((norm_add_le ..).trans (add_le_add_right (show ‖x • v.l‖≤ _ from (by simpa only [pow_one] using he 1 v.l)) _)) (he 2 v.h)); exact hz.trans (by linarith)
lemma CandK (x:ℝ)(h:|x| ≤ 1)(i:ℕ)(hi:1 ≤ i)(hp:i≤3): ‖iteratedFDeriv ℝ i (v.atK) x‖≤ (3*TagN v)^i:=by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; have he(i:ℕ)(hi:1 ≤ i): 3*TagN v≤ (3*TagN v)^i:=(pow_one _).symm.trans_le (pow_le_pow_right₀ (by linarith only [VatR v]) hi); apply le_trans _ (he i hi); interval_cases i
      · rw [iteratedDeriv_one,(Jline ..).deriv, wheelD]; refine (norm_add_le ..).trans ?_; rw [norm_smul,norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,abs_of_nonneg (by norm_num)]; unfold TagN; nlinarith only [norm_nonneg v.s,norm_nonneg v.l,norm_nonneg v.h,mul_le_mul_of_nonneg_right h (norm_nonneg v.h)]
      · rw [Wwheel,norm_smul]; norm_num; unfold TagN; nlinarith only[norm_nonneg v.s,norm_nonneg v.l,norm_nonneg v.h]
      rw [show iteratedDeriv 3 v.atK=deriv (fun _=> (2:ℝ) • v.h) from (iteratedDeriv_succ ..).trans (congr_arg _ (funext fun i=> Wwheel v i))]; simp; linarith [VatR v]
-- visible+t wall; `ball` margin needed only for lip
lemma Flare (D R C:ℝ)(h:ContDiff ℝ 3 p)(hp:TagN v+D ≤ R)(hD:0≤D)(hC:0≤C)(hc:∀ i:ℕ,i ≤ 3→∀ x:E,‖x‖≤R→ ‖iteratedFDeriv ℝ i p x‖≤ C)(w:E)(t:ℝ)(ht:0<t)(hV:t≤1)(hu:‖w-v.atK t‖≤D*t^3):
     ‖p w-(Jpiece v p).atK t‖ ≤ (C*D+ (Nat.factorial 3:ℝ)*C*(3*TagN v)^3)*t^3:=by
       let f:= p ∘ v.atK; have hx:C*(TagN v)≥0:=mul_nonneg hC (zero_le_one.trans (VatR _)); have hh:= paceT f t ht 2 (h.comp ((kernelS v).of_le le_top)) ((Nat.factorial 3:ℝ)* C*(3*TagN v)^3) (by have he:=VatR v; have hp:0 ≤TagN v:= zero_le_one.trans he; positivity) (fun a ha=> ?_); swap
       · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; let Q:=3* TagN v; have hz:|a|≤1:=by rw [abs_of_nonneg ha.1]; exact ha.2.trans hV
         exact strap v.atK p a 3 ((kernelS v).contDiffAt.of_le le_top) h.contDiffAt C Q (fun i hi=> hc i hi (v.atK a) ((Spat v a hz).trans (le_trans (le_add_of_nonneg_right hD) hp))) (CandK v a hz)
       have he:∑ i∈range (2+1),t^i * WardBin.leading i f=(Jpiece v p).atK t:=by
            have ht(u:Char.Phase): WardBin.leading u.val f=(Jpiece v p).seq u.val:= brightX v (h.of_le (by norm_num)) u; simp only [sum_range_succ,sum_range_zero]; erw [ht 0, ht 1, ht 2]; simp only [pow_zero,pow_one,one_mul,zero_add]; rfl --
       rw [he] at hh; have hw: ‖v.atK t‖≤ TagN v:= Spat v t (by rw [abs_of_pos ht]; exact hV); have ha: TagN v≤R:=le_trans (le_add_of_nonneg_right hD) hp
       have hy: ‖w‖ ≤ R:= ((norm_le_norm_add_norm_sub (v.atK t) w).trans (add_le_add hw (((norm_sub_rev (v.atK t) w).trans_le hu).trans (mul_le_of_le_one_right hD (pow_le_one₀ ht.le hV))))).trans hp -- wrong syntax
       have hm:‖p w - p (v.atK t)‖ ≤ C * ‖w-v.atK t‖:= by
            exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun u _=> h.differentiable (by norm_num) u) (fun x hx=> (norm_iteratedFDeriv_one _).symm.trans_le (hc 1 (by norm_num) x (mem_closedBall_zero_iff.mp hx))) (convex_closedBall 0 R) (mem_closedBall_zero_iff.mpr (hw.trans ha)) (mem_closedBall_zero_iff.mpr hy)
       apply (norm_sub_le_norm_sub_add_norm_sub _ (f t) _).trans; rw [add_mul]; exact add_le_add (hm.trans ((mul_le_mul_of_nonneg_left hu hC).trans_eq (mul_assoc ..|>.symm))) hh
end
end YM.OPE.Spells
