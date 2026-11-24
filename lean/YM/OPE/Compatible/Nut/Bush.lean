import YM.OPE.Compatible.Nut.Fig
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
open Source Labels Extra.Multi
variable {n:Side}{k b:ℕ}{X: Labels.Frame G k} (S:SectionData X)(o:Site n) {R:Rep G n}{h:Hol G}{a b' c:ℝ}
open Extra.Histories
-- a request for each unit-normalized label; support cut covers.
structure Cache (P:X.Coeff→ Coefficient X n)(a C t:ℝ):Prop where
       data : Ledger X n P
       pet v: Pet o S (P v) a t (C * X.coeffSize (X.core v)) (H:=h) (R:=R)
       mark v:(P v).x=v
variable {P:X.Coeff → Coefficient X n}{I:Finset ℕ} {t C:ℝ}
lemma GroveL (P:X.Coeff→ Coefficient X n) (H:Ledger X n P): IsLinearMap ℂ (fun x:X.Coeff=> GroveV o S (P x) I R):=by
       let f(x:X.Coeff):= S.places x o; have hf:IsLinearMap ℂ f:=by
             unfold f SectionData.places; constructor
             · intro x y; funext v; rw [S.eval_linear.map_add]; rfl
             intro a x; funext v;rw[S.eval_linear.map_smul];rfl
       let g(x):=(X.scaled R.p.threshold⁻¹ (P x|>.x)); constructor
       · intro x y; change f (g (x+y)) + _= _; rw [show g (x+y)= _ from (show g (x+y)=g x+g y from by unfold g; rw [H.x.map_add,map_add]), hf.map_add, H.reg.map_add]; unfold GroveV; simp_rw [Pi.add_apply, Finset.sum_add_distrib]; unfold g f; abel
       intro a x; change f (g (a • x)) + _= _; rw [show g (a • x)= _ from (show g (a • x)=a • g x from by unfold g; rw[H.x.map_smul,map_smul]), hf.map_smul, H.reg.map_smul]; unfold GroveV; simp_rw [Pi.smul_apply, smul_add, Finset.smul_sum]; rfl -- simp maybe
-- assembly caches
variable {S o}
local notation "Y"=> X.Index
noncomputable abbrev CastX {k:ℕ}{X:Labels.Frame G k}(x:X.Index): X.Coeff:=Pi.single x 1
noncomputable abbrev clove (X:Labels.Frame G k)(t:ℝ) (p:X.Coeff):= ∑ i:X.Index,‖p i‖*(1+t*X.coeffSize (X.core (CastX (X:=X) i)))
variable (hP:Cache S o (R:=R) (h:=h) P a C t) (hT:S.Sound h) (hz:S.stencil ⊆ Lattice.box b) (hB:budgetK R.p.B ≤ b)
def LampO (I:Finset ℕ):Prop:=∀ v:X.Coeff, Shoo o S (P v) b I∧∀ U, Healthy R.p.threshold (Spindle.patch b o) U→ ‖(P v).exponentialEntry o S R U-GroveV o S (P v) I R U‖ ≤ clove X C v*Ξoff R.p
include hP hT hz hB
lemma giftQ : ∃ I:Finset ℕ,LampO (o:=o) (S:=S) (C:=C) (R:=R) (b:=b) (P:=P) I:=by
       have he: S.footprint o ⊆ Spindle.patch b o:=by rw [patch_eq]; exact Finset.image_subset_image hz
       obtain ⟨q,hq⟩:= (Filter.eventually_all.mpr (fun i:Y=> Beacon S o (P (CastX (X:=X) i)) (hP.pet _) hT he hB)).exists; let B(i):=coverNumber R.p.B ((P 0).support i); let J:= q.filter (fun i=> B i≤R.p.B); refine ⟨J,fun i=>⟨⟨?_,hz⟩,?_⟩⟩
       · intro m hm; apply (stemQ S o (P i) (hP.pet i) J ?_ _ hm).trans (Corona.halo_mono hB (Finset.Subset.refl _)); intro j hi; rw [hP.data.tags]; exact (Finset.mem_filter.mp hi).2
       intro v hV; let f(x:X.Coeff):=(P x).exponentialEntry o S R-GroveV o S (P x) J R; let g(i:X.Coeff):= GroveV o S (P i) J R; let F : X.Coeff→ₗ[ℂ] (Config G n→ℂ):=(YM.MergeProof.expoLinear (T:=S) P (fun i=>_ ) hP.data (fun i=>(hP.pet i).cap)|>.mk' _)-(GroveL (I:=J) (R:=R) S o P hP.data).mk' g -- mk' syntax
       have hp : F i= ∑ j:Y, i j • F (CastX (X:=X) j) :=by
                apply Eq.trans (congr_arg F (show i=∑ j:Y,i j • CastX (X:=X) j from ?_)) _; swap; · rw[_root_.map_sum]; exact Finset.sum_congr rfl fun j _=> F.map_smul ..
                funext p; simp [CastX,Pi.single_apply,Finset.sum_apply]
       have hh(j:Y): ‖F (CastX (X:=X) j) v‖≤ (1+C * X.coeffSize (X.core (CastX (X:=X) j)))*Ξoff R.p:=by
               rw [mul_comm]; let i:=CastX (X:=X) j; let J':= q.filter fun x=>coverNumber R.p.B ((P i).support x) ≤ R.p.B; have hj:J'=J:=by unfold J J' B; rw[hP.data.tags]; -- hP tags loops rewrites only one
               change ‖(P i).exponentialEntry o S R v-GroveV o S (P i) J R v‖≤_; rw[←hj]; exact hq j v hV
       change ‖F i v‖≤_; rw[hp,Finset.sum_apply]; apply (norm_sum_le ..).trans; unfold clove; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j _=>?_ ; rw [Pi.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left (hh j) (norm_nonneg _)).trans_eq (mul_assoc ..|>.symm)
end
end Zest
end YM.OPE.Lass
