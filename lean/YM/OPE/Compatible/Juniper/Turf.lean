import YM.OPE.Compatible.Juniper.Bike
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
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
variable {τ:Char.Phase→ℕ}{P:Pad G}{R:BudgetPoint}{v:Train i}
section
variable (P) {z ξ t:ℝ} (h:2*(b+1)<n.val) (U:BudgetPoint)(f:Config G n→ℂ)(a: ℂ→L[ℝ] ℝ)
noncomputable abbrev breezeL (G:Gauge)(b:ℕ)(t:ℝ) : Scoop G b →L[ℝ] DrawerB G b:= t • (strideG G b).symm.toContinuousLinearMap
abbrev Θrank (y s:ℝ):= y*s⁻¹
-- feed R.T.S.Frame at phase0.P.Ph normalized (ξ/threshold)
noncomputable abbrev Artifact (ξ:ℝ):Scoop G b→ℝ := a ∘ (LaunchB o P h U f) ∘ (breezeL G b (Θrank ξ U.threshold))
lemma filip (ξ:ℝ)(hs:U.Regular (Spindle.patch b o) f): ContDiff ℝ U.order (Artifact o P h U f a ξ):= a.contDiff.comp ((smooth2B o P h U f hs).comp (breezeL G b _|>.contDiff))
def basicT (P:Pad G)(ξ:ℝ) (b j:ℕ)(U:BudgetPoint)(a:ℂ→L[ℝ]ℝ)(c:ℝ):= ‖a‖* ((lights P j|>.choose)*sizeQ b ^ j*c) *((strideSize G|>.choose)*‖Θrank ξ U.threshold‖)^j
lemma apriced (hp:Widen U b)(hs:U.Regular (Spindle.patch b o) f)(ht:U.supBounds o (Spindle.patch b o) f t)(hi:k ≤ U.order)(ξ:ℝ)(x:Scoop G b): ‖iteratedFDeriv ℝ k (Artifact o P h U f a ξ) x‖ ≤ basicT P ξ b k U a t:=by
       let T:=LaunchB o P h U f; let A:= breezeL G b (Θrank ξ U.threshold); have he:ContDiff ℝ k T:=(smooth2B o P h U f hs).of_le (Nat.cast_le.mpr hi); unfold basicT; apply graphP (a∘T) A x k (a.contDiff.comp he).contDiffAt
       · refine (a.norm_iteratedFDeriv_comp_left he.contDiffAt (le_refl _)).trans ?_; exact mul_le_mul_of_nonneg_left ((lights P k).choose_spec.2 n b h o U f t _ hp hi hs ht) (norm_nonneg _)
       unfold A; rw [breezeL,norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_right ((strideSize G).choose_spec.2 b|>.2) (norm_nonneg _)
structure Acceptance (k:ℕ)(f:Config G n→ℂ)(b:ℕ)(t:ℝ):Prop where
       guard : k ≤ U.order
       Shush : Widen U b
       ready : U.Regular (Spindle.patch b o) f
       toll : U.supBounds o (Spindle.patch b o) f t
lemma impeccable (F:Acceptance o U k f b t)(ξ:ℝ): Stature (Artifact o P h U f a ξ) k:= Stature.borne (a:=fun j=>basicT P ξ b j U a t) ((filip o P h U f a ξ F.ready).of_le (Nat.cast_le.mpr F.guard)) (fun _ hi x=>apriced o P h U f a F.Shush F.ready F.toll (hi.trans F.guard) ξ x)
variable (K:KernelChoices)(v:Train i) (hp:4 ≤ i)(Λ:ℝ)
noncomputable abbrev OrionV (F:Acceptance o U k f b t):=CurveG (Vessel K v G n hp) (Measure.addHaar) (Cane G b o) _ (impeccable o P h U f a F Λ)
lemma δHue (ξ:ℝ)(hf:GaugeInvariant f)(t:G.El)(x:Scoop G b) : Artifact o P h U f a ξ (rotaryB G b t x)= Artifact o P h U f a ξ x:=by
       let c:= Θrank ξ U.threshold; let S:=crevy (G:=G) (b:=b) t; refine congrArg a ?_; let T:= (strideG G b).symm; change LaunchB _ _ _ _ _ (c • T (strideG G b (S (T x))))= LaunchB _ _ _ _ _ (c • T x)
       rw [show T _ =_ from (strideG G b).symm_apply_apply _, ← _root_.map_smul S]; exact HearthY o P h U f hf _ _ -- hx
lemma Recon (F:Acceptance o U k f b t): ReadyP (OrionV o P h U f a K v hp Λ F) k:=by
       let V:= Vessel K v G n hp; let X:= Cane G b o; let p:=OrionV o P h U f a K v hp Λ F; let g:= Artifact o P h U f a Λ; have hq:p∈harmon (Scoop G b) k:=TurnedT ..; constructor; exact hq
       intro i x u; let T:=rotaryB G b u; have he: (Strike k p) ∘ T=Strike k p:=funext fun y=> incentive V Measure.addHaar X T (clans o u v hp K b) g (impeccable o P h U f a F Λ) (funext fun y=> δHue o P h U f a Λ F.ready.symmetry u y) y; let Q j:=(p j).compContinuousLinearMap (fun _=> T); have ht: Q∈ harmon _ k:=eer T p Q (fun _=>rfl) hq; exact DFunLike.congr_fun ((gradeC ht i).symm.trans ((congr_arg (fun f:Scoop G b→ℝ =>coeff f i 0) (show Strike k Q=Strike k p from he)).trans (gradeC hq i))) x
variable (F:Acceptance o U k f b t)
noncomputable abbrev TourF (Λ:ℝ):= ∑ j∈range (k+1),basicT P Λ b j U a t -- b.F needed
lemma clothV (j:ℕ)(ht:j ≤ k): ‖OrionV o P h U f a K v hp Λ F j‖ ≤ wakeY k (Fpaper G b) (-(1/2)) (cookV G v K hp n b)* TourF P U a (t:=t) (b:=b) (k:=k) Λ :=by
       let V:=Vessel K v G n hp; let S:=Cane G b o; let X:= chamber V S; let B(j):= basicT P Λ b j U a t; let p:= Artifact o P h U f a Λ; have he:= impeccable o P h U f a F Λ; have hv:0≤ cookV G v K hp n b:=by unfold cookV;apply mul_nonneg (mul_nonneg (rentV G v hp K n).positive ?_) (sq_nonneg _); exact sq_nonneg _
       have ht'(i)(hi:i ≤ k): ‖FarG V Measure.addHaar S he i‖ ≤ B i:= Palet V Measure.addHaar S he i hi (fun p=>apriced o P h U f a F.Shush F.ready F.toll (hi.trans F.guard) Λ p)
       apply Woper X _ _ _ hv (FarG V Measure.addHaar S he) (WealthF ..) _ (avenue o v K hp b) _ ht
       intro i hi; exact (ht' i hi).trans (single_le_sum (f:=B) (fun i hi=> (norm_nonneg _).trans (ht' i (Nat.le_of_lt_succ (mem_range.mp hi)))) (mem_range.mpr (by omega)))
end
end YM.OPE.Spells
