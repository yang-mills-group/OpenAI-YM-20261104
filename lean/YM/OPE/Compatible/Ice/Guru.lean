import YM.OPE.Compatible.Ice.Axe
/-! # unshift register by orientation transition, preserving budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d e:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section
variable (G)(H:Aware d τ)
local notation "W!"=>solar G d τ
noncomputable def vintage (t:ℝ):solar G d τ→L[ℝ] solar G d τ:= (rebase G H t ∘L (solar G d τ).subtypeL).codRestrict _ (fun i=> Drift.aboard _ H i.val i.property) -- correct args
lemma truthR (t:ℝ)(p:W!): (vintage G H t p).val=rebase G H t p.val:=rfl
lemma toneR (t:ℝ)(p:W!): vintage G H t p=p+t • (vintage G H 1 p - p):=by
       let V:=p.val; refine Subtype.ext (funext (fun i=>?_)); change rebase G H t V i= V i+t • (rebase G H 1 V i - V i); by_cases hz:i=2; swap; · rw [sail t i H V hz,sail 1 i H V hz,sub_self,smul_zero,add_zero]
       subst i; rw [Drift.sip,Drift.sip, add_sub_cancel_left,smul_smul];ring_nf
lemma vou (t:ℝ)(p:W!): vintage G H t (trellisA G H p)=trellisA G H (vintage G H t p):=Subtype.ext (gaze H p.val _|>.symm)
lemma via (t c:ℝ)(p:W!): vintage G H t (Ripple G H c p)=Ripple G H c (vintage G H t p):=by rw [twig,twig]; simp only; rw [map_add,map_add,map_smul,map_smul,vou,vou]
lemma undo (t:ℝ)(p:W!): vintage G H t (vintage G H (-t) p)=p:= by apply Subtype.ext; rw [truthR,truthR,successive,add_neg_cancel, Drift.salute] -- actual salute
noncomputable abbrev KevT (d:ℕ)(x q:ℝ):= q + ‖x/2‖*((d:ℝ)*q)
lemma vintage_hi (t:ℝ)(p:W!)(hp:Tide (Goan p) d m r): Tide (Goan (vintage G H t p)) d m (KevT d t r):=by
       let q(i:Phase):= (Goan p) i; let V:=p.val; have hz : 0 ≤ r:= Sack.coins ((hp 0).2 0); have ht:r≤ KevT d t r:= le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) hz)); intro i; change Volume (lilies _ _ _ (rebase G H t V i)) (d+i.val) _ _; by_cases he:i=2; swap; · rw[sail t i H V he]; exact (hp i).raise _ le_rfl ht
       subst i; rw[Drift.sip,map_add,map_smul]; refine Volume.add _ (hp 2) (Volume.spread _ _ ?_); let v(i:ℕ):= (i:ℝ) • q 0 i; have hh:=funext fun i=> peak_eq (V 0) H i; rw [show lilies _ _ _ (_)=v from (show lilies (τ 2) _ _ (peakV G H (V 0))= v from hh)]; refine Volume.raise v ?_ (show d≤ d+(2:Phase).val from by omega) le_rfl -- remove bad
       have hY(j)(hv:d < j):v j=0:=by unfold v; rw [(show q 0 j=0 from (hp 0).1 j hv), smul_zero]
       refine ⟨fun i hi=>hY i hi,fun i=>?_⟩; by_cases he:i≤d
       · exact Sack.tips (Sack.scale_line ((hp 0).2 i) (i:ℝ)) (mul_le_mul_of_nonneg_right (by rw [Real.norm_natCast];exact_mod_cast he) hz)
       rw [hY i (not_le.mp he)]; exact Sack.zero (mul_nonneg (Nat.cast_nonneg _) hz) _
end
end YM.OPE.Ibis
