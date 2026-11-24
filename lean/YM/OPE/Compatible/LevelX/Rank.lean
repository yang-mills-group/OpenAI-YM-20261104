import YM.OPE.Compatible.Broma.Pep
/-! # Grade taps. lifts and kernels -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
-- dimension.K
example (G:Gauge)(k:ℕ): FiniteDimensional ℝ (Alphabet G k):=inferInstance
example (G:Gauge) (r n d:ℕ): FiniteDimensional ℝ (partX G r n d):=inferInstance
abbrev TagW (G:Gauge)(d e r:ℕ):= PAD (Fin (Module.finrank ℝ (partX G r (e-r) d)))
noncomputable def coordinateQ (G:Gauge)(d e r:ℕ):partX G r (e-r) d ≃ₗ[ℝ] TagW G d e r:=by letI he :Module.Free ℝ (partX G r (e-r) d):=Module.Free.of_divisionRing ℝ (partX G r (e-r) d); exact (finBasis ℝ (partX G r (e-r) d)).equivFun
local notation "B!"=> bed G k m
-- pull p⇝ key
noncomputable def terrace (G:Gauge)(k m r:ℕ): bed G k m→ₗ[ℝ] cope G r m where
     toFun p:= ⟨lilies m k (Shade G) p.val r,p.property r⟩
     map_add' p q:=Subtype.ext (congr_fun (map_add _ p.val q.val) _)
     map_smul' c p:=Subtype.ext (congr_fun (map_smul (lilies m k (Shade G)) c p.val) _)
-- W read
noncomputable def grasps (G:Gauge)(d e k m r:ℕ)(h:e-r≤m): bed G k m →ₗ[ℝ] TagW G d e r:= (coordinateQ G d e r).toLinearMap ∘ₗ Flume.Script.tiller G r m (e-r) h d ∘ₗ terrace G k m r
lemma whiff (A:Fin r→ fieldX (Shade G))(x:Fin r→ℕ)(hp:Glob A x)(h:∑ i,x i ≤ m):Continuous (fun b:B! => wholeX (terrace G k m r b).val A):=by
     let f:= terrace G k m r; let p(b:B!):= lilies _ _ _ b.val r; let X:B!→ₗ[ℝ] ℝ:={ toFun b:=wholeX (p b) A,map_add' i j:= by rw [show p _=p i+p j from congr_fun (map_add ..) _]; exact manyX (patent_till (f i)) (patent_till (f j)) hp h,map_smul' c v:=by rw [show p _=c • p v from congr_fun (map_smul ..) _]; exact scaleX .. }
     choose a ha H using fun x=>hp x; let D:= ∏ i,a i; have hd:0≤D:= prod_nonneg (fun i _=>ha i); change Continuous X; refine (X.mkContinuous D (fun u=>?_)).continuous; have hv := sproutV m k u.val|>.2 r; change ‖wholeX _ _‖ ≤ _; apply (norm_tsum_le_tsum_norm (wordSum hv hp h|>.norm)).trans; let T(i):= Page.figure m i*‖p u i‖; have hz(i:Page (Shade G) r): ‖p u i*wordX A i‖≤ D*T i :=by rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (wordXbill ha H h _) (norm_nonneg _)).trans_eq; unfold D T;ring
     apply ((wordSum hv hp h|>.norm).tsum_le_tsum hz (hv.2.1.mul_left D)).trans; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hv.2.2 hd
end YM.OPE.Drift
