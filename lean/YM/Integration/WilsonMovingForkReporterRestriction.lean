import YM.Integration.WilsonMovingForkReporterPanelCourse

/-! Restriction of one returned weak table to a smaller horizon on its original apertures. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRestriction
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {d D:ℕ} (within:d≤D) (V:Vane C D)
  {f:Extraction.Order} {H:(Cells.standard C).Hierarchy}

def slot (i:Fin (d+1)):Fin (D+1) := ⟨i.val,by omega⟩

def vane : Vane C d := ⟨V.k,V.b,V.c,fun N per i => V.R N per (slot within i)⟩

theorem row (N per:ℕ) (i:Fin (d+1)):
    (vane within V).wheel.atCut (N,per) i = V.wheel.atCut (N,per) (slot within i) := rfl

theorem checked (paid:V.checked f H D):(vane within V).checked f H d:=by
  have aperture:sizeHint d≤ sizeHint D:=by unfold sizeHint;exact_mod_cast Nat.add_le_add_right within 1
  have small:0< sizeHint d:=by unfold sizeHint;positivity
  have price:costHint D≤ costHint d:=(inv_le_inv₀ (small.trans_le aperture) small).2 aperture
  have radius (n:ℕ):Scaling.window (sizeHint d) n ⊆ Scaling.window (sizeHint D) n:=by
    rintro y ⟨apart,length⟩
    exact ⟨fun i j h=>price.trans (apart i j h),length.trans aperture⟩
  refine ⟨paid.high,fun u=>paid.early (slot within u),fun N per live=>?_,?_,?_⟩
  · obtain ⟨charts,fare⟩ := paid.rate N per live
    exact ⟨fun i=>charts (slot within i),fun i=>fare (slot within i)⟩
  · refine ⟨paid.plate.width,fun w p N per hn x fitted h s nonempty=>?_⟩
    exact (paid.plate.boot (slot within w) p N per hn x fitted h s nonempty).trans price
  · constructor
    · obtain ⟨A,receipt⟩:=paid.fares.lift_bound
      refine ⟨A,?_⟩
      filter_upwards [receipt] with p live
      filter_upwards [live] with N current
      refine le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg (V.wheel.atCut (f.mesh N,f.per p)))).mpr ?_) current
      exact fun i=>norm_le_pi_norm (V.wheel.atCut (f.mesh N,f.per p)) (slot within i)
    · exact paid.fares.lift_unit
    · filter_upwards [paid.fares.lift_real] with p readings
      filter_upwards [readings] with N axes
      exact fun i=>axes (slot within i)
    · filter_upwards [paid.fares.lift_signed] with p readings
      filter_upwards [readings] with N axes
      exact fun i=>axes (slot within i)
    · intro n hn v hv t support M positive gross
      have amount:0≤Next.UVStress.Station.charge v := Finset.prod_nonneg (fun i _=>norm_nonneg _)
      have fee:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right price amount) positive.le
      have receipt:=paid.fares.short (hn.trans within) v (fun i=>(hv i).trans within) t
        (support.trans (radius n)) M positive gross
      intro η hη
      filter_upwards [receipt η hη] with p readings
      filter_upwards [readings] with N quote
      exact quote.trans (add_le_add_left fee η)

end YM.Integration.WilsonMovingForkReporterRestriction
end
