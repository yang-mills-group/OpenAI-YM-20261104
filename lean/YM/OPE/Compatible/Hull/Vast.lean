import YM.OPE.Compatible.Hull.Air
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
variable (H:Hol G){d:ℕ}
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
lemma RateV (A:Snap G d)(k:ℕ):∃ C:ℝ,∃ p:ℕ,0 ≤ C ∧∀ b:ℕ,∀ θ:ℝ,0 < θ→θ ≤1→ ContDiffAt ℝ k (sprintD H b θ A) 0 ∧ sprintD H b θ A 0=0 ∧ ‖iteratedDeriv k (spanT H b A) 0‖ ≤ C*(1+(b:ℝ))^p ∧ ‖iteratedDeriv k (sprintD H b θ A) 0-iteratedDeriv k (spanT H b A) 0‖ ≤ C*(1+(b:ℝ))^p*θ:=by
        obtain ⟨C,hc,h⟩:= PriceB (flash A) k (flashZ A) ((flashDiff (n:=k) A).contDiffAt)
        choose U v hU V using fun i=> GlassS H i d
        let m:=max 1 k; obtain ⟨F,w,hF,Hx⟩:= artillery U v m hU; refine ⟨F*C,w,mul_nonneg hF hc,fun b θ ht hh=>?_⟩; let X:=1+(b:ℝ); have hp:1 ≤ X:=le_add_of_nonneg_right (Nat.cast_nonneg _); obtain ⟨hP,hq,hi⟩:= V m b; obtain ⟨hS,hD,hT⟩:=h (Scoop G b) (burstQ H b) (F*X^w) θ (mul_nonneg hF (pow_nonneg (zero_le_one.trans hp) _)) hq ht hh (fun i hi=>(V i b).2.2.trans (Hx _ hp i hi)) hP; change ‖iteratedDeriv k (sprintD H b θ A-spanT H b A) 0‖≤ F*X^w*C* θ at hT; rw [show F*X^w*C=F*C*X^w from by ring] at hS hT; rw [iteratedDeriv_sub (show ContDiffAt ℝ k (sprintD H b θ A) 0 from hD) (show ContDiffAt ℝ k (spanT H b A) 0 from (fderiv ℝ (burstQ (d:=d) H b) 0).contDiff.contDiffAt.comp _ ((flashDiff (n:=k) A).contDiffAt)) ] at hT; exact ⟨hD,by simp only[sprintD,Pi.smul_apply,Function.comp_apply,flashZ,smul_zero]; exact (congr_arg _ hq).trans (smul_zero _),hS,hT⟩
structure KiteB (H:Hol G)(B:Snap G d)(θ:ℝ)(o b:ℕ)(C:ℝ):Prop where
        pos : 0 ≤ C
        smooth : ContDiffAt ℝ o (sprintD H b θ B) 0
        zeroP : sprintD H b θ B 0=0
        bump i (hi:i ≤ o): ‖iteratedDeriv i (spanT H b B) 0‖≤ C
        bump' i (hi:i ≤ o): ‖iteratedDeriv i (sprintD H b θ B) 0‖≤ C
        dif i (hi:i ≤ o): ‖iteratedDeriv i (sprintD H b θ B) 0-iteratedDeriv i (spanT H b B) 0‖≤ C*θ
lemma RayV (B:Snap G d)(k:ℕ): ∃ C:ℝ,∃ v:ℕ,0 ≤ C ∧∀ b:ℕ,∀ t:ℝ,0<t→ t ≤1→ KiteB H B t k b (C*(1+(b:ℝ))^v):=by
       choose C v hC V using fun i=> RateV H B i; obtain ⟨D,w,hD,L⟩:=artillery C v k hC; refine ⟨D+D,w,add_nonneg hD hD,fun b t ht hh=>?_⟩; let X:=1+(b:ℝ); have hx:1 ≤ X:=le_add_of_nonneg_right (Nat.cast_nonneg _); let U:=D*X^w; have hu:0 ≤ U:=mul_nonneg hD (pow_nonneg (zero_le_one.trans hx) _); rw [add_mul]; let V(i:ℕ):= V i b t ht hh; refine ⟨add_nonneg hu hu,(V k).1,(V k).2.1,fun i hi=> (V i).2.2.1.trans ((L X hx i hi).trans (le_add_of_nonneg_right hu)),fun i hi=>?_, fun i hi=> (V i).2.2.2.trans (mul_le_mul_of_nonneg_right ((L X hx i hi).trans (le_add_of_nonneg_right hu)) ht.le)⟩
       let p:=iteratedDeriv i (sprintD H b t B) 0; let q:=iteratedDeriv i (spanT H b B) 0; change ‖p‖ ≤ _; rw [show p=p-q+q from (sub_add_cancel ..).symm]; apply (norm_add_le ..).trans ; exact add_le_add ((V i).2.2.2.trans ((mul_le_mul_of_nonneg_right (L X hx i hi) ht.le).trans (mul_le_of_le_one_right hu hh))) ((V i).2.2.1.trans (L X hx i hi))
end
end YM.OPE.Spells
