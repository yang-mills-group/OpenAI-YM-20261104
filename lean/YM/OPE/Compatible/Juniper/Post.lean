import YM.OPE.Compatible.Juniper.Toon
/-! # run-weir supply. -/
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
variable {t ζ F:ℝ}
variable (P:Pad G) (h:2*(b+1)<n.val)(U:BudgetPoint) (f:Config G n→ℂ)(a:ℂ→L[ℝ] ℝ)(K:KernelChoices)(v:Train i) (hp:4 ≤ i)(Λ:ℝ)
variable (Q:Acceptance o U (k+6) f b t)
-- film full.Partner.Heavy
noncomputable abbrev Incl (x:fieldX (Shade G)):= Autum (Artifact o P h U f a Λ) x
noncomputable abbrev RestD (x:Fλ) := Autum ((Artifact o P h U f a Λ)-runG (Vessel K v G n hp) Measure.addHaar (Cane G b o) _ (impeccable o P h U f a Q Λ)) x
lemma weds {τ:Phase→ℕ}(H:Aware (k+6) τ) (V:Bid.Dir G n):
      let M:= charW o V; let _p:=OrionV o P h U f a K v hp Λ Q
      let A:= ChiselV H (Recon o P h U f a K v hp Λ Q)
      Incl o P h U f a Λ M= inkM (Drift.spread G (k+6) τ A.val) (k+6) o V + RestD o P h U f a K v hp Λ Q M :=by
            intro w p A; rw [radiates o V (Recon ..) H]; let y:=Artifact o P h U f a Λ; let q:= Strike (k+6) p; change Jpiece (BFilm b w) y=Jpiece _ q+ Jpiece _ (y-q); have hz:= (sailCost p (k+6)).cost; have he : Stature (y-q) (k+6):=(impeccable o P h U f a Q Λ).sub (Stature.poly hz _); rw[← sectorJ q (y-q) (BFilm b w) (hz.smooth.of_le le_top) ((he.smooth.of_le (Nat.cast_le.mpr (by omega)))), add_sub_cancel] -- ≠ er
-- chart s. Art = f on small links, direct expansion; assumes small enough W there
include Q
lemma chanting (x: Config G n)(hc:Λ ≠0)(s:ℝ)(hs:0 ≤ s)(he:∀ i: Dim o (4*b), G.chord (x i.val) ≤ s)(ht:Belts b*s≤ P.B)(hA:sizeQ b*(U.threshold⁻¹*(Belts b*s))^2 ≤ P.r^2/2):
      Artifact o P h U f a Λ (Exposure b (Λ⁻¹ • board (expandAt o x)))=a (f x):=by
            let t:=U.threshold; have hx:= braceY o P h U x s hs he ht hA f Q.ready; let V:= board (expandAt o x); let y:= Λ⁻¹ • V; let z:= U.threshold⁻¹ • V; let c:= (strideG G b); refine congr_arg a ((congr_arg (LaunchB o P h U f) ?_).trans hx); change (Λ*t⁻¹) • c.symm (c (InLine b y))= socket b (InLine (4*b) z); rw [ContinuousLinearEquiv.symm_apply_apply,←map_smul,show (Λ*t⁻¹) • y=z from by unfold y z t; rw [smul_smul,show _*_ =U.threshold⁻¹ from ?_]; ring_nf; field_simp,homeB]; exact funext fun i=>(congr_arg (indexS i.val) (sourceU _ _).symm).trans (champ i.val z).symm
lemma landscape (V: Bid.Dir G n)(hc:0<Λ)(hS:Λ ≤1) (s:ℝ)(hs:0 ≤ s)(he:∀ i:Dim o (4*b),G.chord ((represent (Λ • V)) (i.val)) ≤ s)(hd:3≤ k+6)(ht:Belts b*s ≤ P.B)(hA:sizeQ b*(U.threshold⁻¹*(Belts b*s))^2 ≤ P.r^2/2):
     let M:= charW o V
     ‖a (f (represent (Λ • V)))-(Incl o P h U f a Λ M).atK Λ‖ ≤ Oxone (TagN (BFilm b M)) (AuroraK b M) (TourF P U a (k:=k+6) (b:=b) (t:=t) Λ)*Λ^3:=by
          intro M; let C:=TourF P U a (k:=k+6) (b:=b) (t:=t) Λ; let p:=Artifact o P h U f a Λ; have hh:= impeccable o P h U f a Q Λ; have hz(j:ℕ)(hg:j ≤ k+6)(x:Scoop G b): ‖iteratedFDeriv ℝ j p x‖≤ _:= apriced o P h U f a Q.Shush Q.ready Q.toll (hg.trans Q.guard) Λ x; have hp(j:ℕ)(hg:j ≤ k+6)(x): ‖iteratedFDeriv ℝ j p x‖≤ C:= (hz j hg x).trans (single_le_sum (fun j hj=> (norm_nonneg _).trans (hz j (by have h:= mem_range.mp hj;omega) 0)) (mem_range.mpr (by omega))); rw [← (show _=_ from chanting o P h U f a Λ Q (represent (Λ • V)) hc.ne' _ hs he ht hA)]; rw [← Grid.plank, map_smul]; exact auroraPay p M _ _ ((norm_nonneg _).trans (hp 0 (by omega) 0)) ((hh.mono hd).smooth) le_rfl (fun i hi x _=> hp _ (hi.trans hd) x) _ hc hS
end
-- Norman read. Sensor
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]
variable (v:Train i)(hp:4 ≤ i)(A:E→L[ℝ] Vec G n 1)(ν:Measure E)[ν.IsAddHaarMeasure](B:Law E)
lemma shineD (K:KernelChoices)(b:ℕ)(hz: Licence A B v K)(P:Pad G)(T:BudgetPoint)(w:ℝ)(F:Config G n→ℂ)(a:ℂ→L[ℝ] ℝ)(h:2*(b+1)<n.val){t:ℝ}(Q:Acceptance o T (k+6) F b t)(j:Phase):
     GuardB ν B (k+6-j.val) (k+7-3*j.val) (fun i=> (RestD o P h T F a K v hp w Q (Charu o A i)).seq j.val):=by
         apply Turn_S; exact tSensor _ _ _ _ _ _ (vibrate o v hp K B A hz b) (sensorU (Vessel K v G n hp) Measure.addHaar (Cane G b o) (Artifact o P h T F a w) (impeccable o P h T F a Q w))
end
end YM.OPE.Spells
