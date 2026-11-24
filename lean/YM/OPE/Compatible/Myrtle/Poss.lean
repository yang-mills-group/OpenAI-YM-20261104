import YM.OPE.Compatible.Lamb.Gully
import YM.OPE.Compatible.Sear.Loam
/-! # Studio of regional rotation bookkeeping. Slicing parameters and outgoing ages are separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Raucous
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin Votive Stationary
variable {i m j:ℕ} {s t r R e d b v u z a C:ℝ}
open Zeph Dew
variable {K:Sponsor G}{T:Seasons K}
structure Host (K:Sponsor G)(T:Seasons K) where
     c: Side
     f: Side
     Z: StepData c f
     H: Odd Z.ratio.count.val
     i:ℕ
     v:ℝ
     A:Alps K T i v
     U:Boxes G Z.patch Z.kernel
     b:ℝ
     P:Rep G f
     M : Matrix (Body 1 f) (Body 1 c) ℝ
     g : Bid.Dir G c → AxisChart G (forest Z.ratio H)
     k: Z.Choices
     F:FibreRep Z H U k A g b
-- avoid including hypotheses at creation when eventual. all ∃ Pre.P.D
namespace Host
variable (L: Host K T)
noncomputable abbrev ForestQ := forest L.Z.ratio L.H
abbrev DirA := Bid.Dir G L.c × AxisChart G L.ForestQ
abbrev Dp := Key L.ForestQ G
noncomputable abbrev PA : L.DirA→ℝ:= pane L.ForestQ L.k L.A.clip L.A.live
noncomputable abbrev PL: L.DirA→ℝ := fun x=>springF L.ForestQ L.A.live x.2
abbrev Fund:= FUND L.Z L.H L.U
open Next.SectorChange.Schur Next.Foundations Work.F08 Work.F05 FreeResolvent Pilot
-- make cap represents covariance.Now stave proofs
structure Rich (s b e b' u C:ℝ): Prop where
    home : fitsW L.A L.P
    signed : licensed L.Z L.H L.U L.A.clip L.A.live L.M L.A.sky L.g
    vein : VaultC G s b L.U.C.gap u C
    stem : ∃ p, Pile L.Z L.ForestQ e b s 5 L.PA p
    aged : ∃ p, Pile L.Z L.ForestQ e b' s 3 L.PL p
namespace Rich
variable {b':ℝ}{L:Host K T}(h:L.Rich s b e b' u C)(ht:0<s)(hb:0 ≤ b)(he:0<e)(I:Seats L.ForestQ)
local notation "Fz"=>L.ForestQ
local notation "Xφ"=>Key L.ForestQ G
include h ht hb he
lemma principal {Y:Type}[Fintype Y][DecidableEq Y](A:Y↪ Xφ): Next.SectorChange.Schur.Pours (L.Fund.submatrix A A) (pointK L.Z Fz ∘ A) (pointK L.Z Fz ∘ A) u (limbC G s b) ∧ Gapped (L.Fund.submatrix A A) L.U.C.gap ∧∀ i j, Green.wt u (pointK L.Z Fz (A i)) (pointK L.Z Fz (A j)) * |(L.Fund.submatrix A A)⁻¹ i j| ≤ C := by
        obtain ⟨p,hp⟩:=h.stem; exact spend _ _ _ _ _ _ h.signed A h.vein ht hb he hp (by norm_num)
lemma Burst : Pours L.Fund (pointK L.Z Fz) (pointK L.Z Fz) u (limbC G s b):=by
        obtain ⟨H,_⟩:=principal h ht hb he (Embedding.refl Xφ); simpa only using! H
lemma PourA : Pours (clipRail L.Z Fz I L.Fund) (pointK L.Z Fz ∘ shout G I) (pointK L.Z Fz) (u/2) (porchPrice G u (limbC G s b) C) := torque _ I h.vein.warmth h.vein.broad.le (Burst h ht hb he) ((principal h ht hb he (shout G I)).2.2)
lemma drift (x: Bid.Dir G L.c): ‖L.F.L.M x‖≤ crestPrice G ((flowerC G s u b C)*‖x‖):=by
       obtain ⟨p,hp⟩:=h.stem; have hz:=RegularM L.Z L.H L.A L.U L.k h.signed ht hb he hp (by omega) h.vein; apply Tip_T _ (mul_nonneg hz.pos (norm_nonneg _)); intro i; change ‖cash (countingBasis Fz G) (L.F.L.M x) i‖ ≤ _; rw [Rvoice L.Z L.H L.A L.U L.k L.F h.signed]; exact Hymn _ hz (half_pos h.vein.warmth) (fun j=>Cast_price x j) (norm_nonneg _) i
lemma ripple (x:AxisChart G Fz): ‖ChartUp L.Z Fz I L.F.L.Q x‖≤crestPrice G (porchPrice G u (limbC G s b) C * ‖x‖):= Evoke L.Fund I (h.PourA ht hb he I) (half_pos h.vein.warmth) _ L.F.P0 (ulk_force L.Z L.H L.U) x
lemma Cov_E (x y:Rubric G I): Green.wt u (pointK L.Z Fz (shout G I x)) (pointK L.Z Fz (shout G I y)) * |(PatchM L.Z L.H L.A L.U L.k L.F I).wick (castAt (Tip G (↥I)) x) (castAt (Tip G (↥I)) y)|≤ C :=by
      let A:=L.F.L.Q; have hZ: (plateK L.Z Fz I L.Fund).PosDef := (ulk_force ..).submatrix (shout G I).injective
      rw [coverage _ _ (WithK _ _ I _ A L.F.P0) hZ,Green.wt_symm]; exact (principal h ht hb he (shout G I)).2.2 y x
end Rich
end Host
end YM.OPE.Raucous
