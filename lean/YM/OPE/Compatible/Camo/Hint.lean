import YM.OPE.Compatible.Camo.Pulse
/-! # cancel vintage art against tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer Spells
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
variable {p:Scoop G b→ℝ}
local notation "Fλ"=> fieldX (Shade G)
noncomputable abbrev WSign (p:Scoop G b→ℝ)(w:Fλ)(u:ℝ):= Jpiece (Ebox (BFilm b w) u) p
section
variable {τ:Phase→ℕ}(x:Song (Scoop G b))(H:ReadyP x k)(h:Aware k τ)(u:ℝ)(w:Bid.Dir G n)
private lemma pealW (w:Bid.Dir G n) (b:ℕ):
        let V:= (flats G n).toContinuousLinearMap; BFilm b (charW o w)= BFilm b (Charu o V w):= congr_arg _ (by simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using climbsF o (flats G n).toContinuousLinearMap w)
lemma Stem : inkM (Drift.spread G k τ (rebase G h u (ChiselV h H).val)) k o w= WSign (Strike k x) (charW o w) u:=by
         let p:=Strike k x; let X(y:Bid.Dir G n):= BFilm b (charW o y); let Z:= (flats G n).toContinuousLinearMap; have hx (c:ℝ): (X (c • w)).s=c • (X w).s:=by unfold X; rw [pealW,pealW,flumes,flumes,map_smul,map_smul]
         let q:=Drift.spread G k τ (ChiselV h H).val; have he(y): inkM q k o y=Jpiece (X y) p:= radiates ..; rw [show inkM _ _ _ _=_ from (show inkM (Drift.spread G k τ _) k o w=_ from flot (ChiselV h H).val h u w o),WSign,Ebulb]; simp_rw [show Drift.spread G k τ _=q from rfl,he]; apply congr_arg; have ht: ContDiff ℝ ⊤ p:= (sailCost x k).cost.smooth; let f(t:ℝ):= p ((X (t • w)).s); suffices ha:deriv f 1 = pointD (X w).s p (X w).s by exact congr_arg (fun i:ℝ=> (⟨0,0,(u/2)*i⟩:JetS ℝ)) ha
         rw [show f=fun t:ℝ=> p (t • (X w).s) from funext fun t=>congr_arg p (hx t)]; have hv:= ((ht.differentiable (by norm_num) ((1:ℝ) • (X w).s)).hasFDerivAt).comp_hasDerivAt (1:ℝ) ((hasDerivAt_id' (1:ℝ)).smul_const (X w).s); -- patch
         exact (HasDerivAt.deriv (show HasDerivAt _ _ (1:ℝ) from (by simpa only[Stranded.pointD,one_smul] using! hv)))
variable {t:ℝ}
variable (v:Train i)(hp:4 ≤ i)(P:Pad G)(T:BudgetPoint)(f:Config G n→ℂ)(a:ℂ→L[ℝ]ℝ)(g:ℝ)(hh:2*(b+1)< n.val) (he:Acceptance o T (k+6) f b t)(L:Aware (k+6) τ)
noncomputable abbrev Mell (V:fieldX (Shade G))(u:ℝ):= WSign (Artifact o P hh T f a g) V u
noncomputable abbrev Dark (C:KernelChoices)(V:fieldX (Shade G))(u:ℝ):= WSign (Artifact o P hh T f a g-runG (Vessel C v G n hp) Measure.addHaar (Cane G b o) _ (impeccable o P hh T f a he g)) V u
lemma crossed (w:Bid.Dir G n) (C:KernelChoices)(u:ℝ):
        let A:= ChiselV L (Recon o P hh T f a C v hp g he); let p:=rebase G L u A.val; Mell o P T f a g hh (charW o w) u= inkM (Drift.spread G (k+6) τ p) (k+6) o w+ Dark o v hp P T f a g hh he C (charW o w) u:=by
            intro A p; rw [show inkM _ _ _ _=_ from Stem o (OrionV o P hh T f a C v hp g he) (Recon ..) L u w]; let y:= Artifact o P hh T f a g; let z:= Strike (k+6) (OrionV o P hh T f a C v hp g he); let W:= Ebox (BFilm b (charW o w)) u; have ht : ContDiff ℝ (↑(2:ℕ)) z:= (sailCost ..).cost.smooth.of_le le_top; have hz: ContDiff ℝ (↑(2:ℕ)) y:= (impeccable o P hh T f a he g).smooth.of_le (Nat.cast_le.mpr (by omega)); change Jpiece W y=Jpiece W z+ Jpiece W (y-z); rw [← sectorJ z (y-z) W ht (hz.sub ht),add_sub_cancel]
end
end YM.OPE.Cameo
