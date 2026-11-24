import YM.OPE.Compatible.Hull.Mirror
import YM.OPE.Compatible.Hull.Bevy
import YM.OPE.Compatible.Scrape.Scud
import YM.Extra.MULTISOURCE_BOUNDS.Columns
import YM.OPE.Compatible.LevelX.Fond
import YM.OPE.Compatible.Hull.Nook
import YM.OPE.Compatible.Hull.Spoon
import YM.OPE.Compatible.Hull.Bud
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Source Labels Source.Drops
section
open Beamer Next.Foundations Extra.Multi MvPolynomial
variable {d:ℕ}{H:Hol G}{R:Rep G n} {X: Labels.Frame G d} (T:SectionData X)(v:Coefficient X n)(W:Snap G d)(A:ℂ→L[ℝ]ℝ)
variable {x:Finset ℕ}{a c B:ℝ}
noncomputable def RaySum (s:ℝ→ℝ)(i:Fin (d+1)):ℝ:= ((i.val.factorial:ℝ)⁻¹) * iteratedDeriv i.val s 0
noncomputable def PolyRayX (η:Fin (d+1)→ℝ)(P:Pad G)(A:ℂ→L[ℝ]ℝ)(b:ℕ)(a c:ℝ)(u:BudgetPoint)(v:ℝ):= ∑ i:Fin (d+1),((i.val.factorial:ℝ)⁻¹) * priceArc (η i) P A i.val b a u v c
lemma deskG (S:Shoo o T v b x)(p:Pet o T v a c B (H:=H) (R:=R))(hT:T.Sound H)(hz:10*b<n.val)(hy:2*(4*b+1)<n.val):
      let z(s:ℝ):= A (GroveV o T v x R (south H o W R.p.threshold s)); A (OpticZ (X:=X) v.x W)= ∑ i:Fin (d+1), RaySum z i:=by
           intro z; let u:=X.scaled R.p.threshold⁻¹ v.x; let U:= (south H o W R.p.threshold); let Z:= T.places u o; obtain ⟨he,hp⟩:= viewCost o T R W u hT S.stemmed hy; have hw:X.scaled R.p.threshold u=v.x:= X.scaled_inv R.p.threshold_pos.ne' _; let f:=∑ i∈x,v.regular i; have hx: A ∘ (GroveV o T v x R ∘ U)=A ∘ (Z ∘ U)+ A ∘ (f ∘ U):=by funext i; exact map_add A _ _
           have hg:Reads H o (Spindle.patch b o) (0:Label G d) f:=totalsW o p.form (Spindle.patch b o) x S.supports; have hr: H.PiVanish d o f:= ((reads_null_iff ..).1 hg).2 (fun y ht=>by rw [separation_comm]; exact (Nat.mul_le_mul_left 10 ((doors _).mp ht)).trans_lt hz)
           have ht : z=(A ∘ (Z ∘ U)) + A ∘ (f ∘ U):=hx; obtain ⟨hD,hd⟩:= hr (expand d (R.p.threshold • W)); change ContDiffAt ℝ (↑d:ℕ∞) (f ∘ U) 0 at hD; have hy(i:ℕ)(hi:i ≤ d): iteratedDeriv i z 0=A (iteratedDeriv i (Z∘U) 0):=by
               have hE:ContDiffAt ℝ i (Z∘U) 0:= (show ContDiffAt ℝ d (Z∘U) 0 from he).of_le (Nat.cast_le.mpr hi); have h₁:ContDiffAt ℝ i (f ∘ U) 0:= hD.of_le (by exact_mod_cast hi); rw[ht,iteratedDeriv_add (A.contDiff.contDiffAt.comp _ hE) (A.contDiff.contDiffAt.comp _ h₁),guiding A (Z ∘ U) i _ hE,guiding A _ i _ h₁,show iteratedDeriv i (f ∘ U) 0=0 from hd i hi,map_zero,add_zero]
           rw [hw] at hp; rw [← hp]; unfold Spindle.evaluate_ray; rw [_root_.map_sum, ← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [_root_.map_smul, RaySum,hy i.val (by omega)];rfl
noncomputable def ζSig (W:Snap G d)(t:ℝ)(u:BudgetPoint)(k m:ℕ)(he:d ≤ m) :Seat k m (Shade G)→L[ℝ]ℝ:=∑ i:Fin (d+1), ((i.val.factorial:ℝ)⁻¹) • θFoil W t u k m i.val ((Nat.le_of_lt_succ i.isLt).trans he)
section
variable (S:Shoo o T v b x)(p:Pet o T v a c B (H:=H) (R:=R))(hT:T.Sound H)(hz:10*b<n.val) (hX:2*(b+1)<n.val)(hi:2*(4*b+1)<n.val) (hR:R.p.order ≥ k+6)(hp:Widen R.p b)
variable (P:Pad G)(t:ℝ) (ht:0<t)(η:Fin (d+1)→ℝ)(hE:∀ i:Fin (d+1), KiteB H W R.p.threshold i.val b (η i))
variable (Rz:KernelChoices)(u:Train r)(hr:4 ≤ r)
noncomputable def ArK (v:Coefficient X n)(S:Shoo o T v b x)(p:Pet o T v a c B (H:=H) (R:=R)) (hR:R.p.order ≥ k+6) (P:Pad G)(m:ℕ): bed G (k+6) m:= Locket (Recon o P hX R.p (GroveV o T v x R) A Rz u hr t (Coal o T v p S hR hp)) m
include hT S hz p hi hE ht
-- p threshold true seam; public morph estimate
lemma Perc (he:d < k+6)(hm:d≤ m){ε:ℝ}(hv:∀ q∈ Hoard G (4*b) (k+6) m, ‖boostS (rentV G u hr Rz n) (1/2) m (k+6) q - boostS (atlasF G u hr Rz) (1/2) m (k+6) q‖ ≤ ε*‖q‖):
      let V:= ArK o T A hX hp t Rz u hr v S p hR P m -- order inspect
      let Y:= boostS (atlasF G u hr Rz) (1/2) m (k+6) V.val
      let F:= ζSig W t R.p (k+6) m hm
      ‖A (OpticZ (X:=X) v.x W) - F Y‖ ≤ PolyRayX η P A b (a*X.coeffSize v.x+B) (nubK G b u Rz hr n) R.p t + ‖F‖*(ε*‖V‖):=by
           intro V Y F; let f:= GroveV o T v x R; let Q:Acceptance o R.p (k+6) f b (a*X.coeffSize v.x+B):= Coal o T v p S hR hp; let q:=boostS (rentV G u hr Rz n) (1/2) m (k+6) V.val; let u₀:= A (OpticZ (X:=X) v.x W); have hxV: V.val∈ Hoard G (4*b) (k+6) m:=LayH _ (Recon o P hX R.p f A Rz u hr t Q); refine (norm_sub_le_norm_sub_add_norm_sub u₀ (F q) (F Y)).trans (add_le_add ?_ (show ‖F q-F Y‖ ≤ _ from (show _ from ?_)))
           · unfold u₀ F ζSig; rw [deskG o T v W A S p hT hz hi,_root_.sum_apply,← sum_sub_distrib]; refine (norm_sum_le ..).trans (sum_le_sum (fun i _=>?_)); let w:ℝ:=(i.val.factorial:ℝ)⁻¹; have hx:0≤w:=by unfold w; positivity
             let hC:=hE i; change ‖w * _- w * _‖≤ w *_; rw[← mul_sub,norm_mul, Real.norm_of_nonneg hx]; exact mul_le_mul_of_nonneg_left (chartSignal o W P f t R.p hX Q A Rz u hr ((Nat.le_of_lt_succ i.isLt).trans_lt he) ((Nat.le_of_lt_succ i.isLt).trans hm) (hE i) hi ht) hx
           rw [←_root_.map_sub F]; exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hv _ hxV) (norm_nonneg _))
end
end
end YM.OPE.Spells
