import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFirstTangent

noncomputable section
namespace IssuedBridge.PostedTriangleCutReturns
open Filter Set MeasureTheory
open YM YM.XSpace YM.XSpace.Season YM.XSpace.Chiral
open scoped Topology

theorem sweep (c e : Shade.Cut) (p r m n : Chiral.P) (u v b : E4)
    (hc : Gleam c u v b) (he : Gleam e u v b) :
    Season.sweepT c p r m n u v b = Season.sweepT e p r m n u v b :=
  tendsto_nhds_unique
    (Season.auric c p r m n hc starts (voyage u) (voyage v) (voyage b))
    (Season.auric e p r m n he starts (voyage u) (voyage v) (voyage b))

theorem original (g : YangMills.GaugeGroup) (c e : Shade.Cut) (x : YM.Points 3)
    (hc : x ∈ Photo.Good c 3) (he : x ∈ Photo.Good e 3) :
    YangMills.MSbar.Position.bareTriangle (IssuedMaxwell.Reference.issued g) c x =
      YangMills.MSbar.Position.bareTriangle (IssuedMaxwell.Reference.issued g) e x := by
  have h₁ : Gleam c (x 0) (x 1) (x 2) :=
    ⟨hc 0 1 (by decide), hc 0 2 (by decide), hc 1 2 (by decide)⟩
  have h₂ : Gleam e (x 0) (x 1) (x 2) :=
    ⟨he 0 1 (by decide), he 0 2 (by decide), he 1 2 (by decide)⟩
  have eq (p r m n : Chiral.P) :
      Season.sweepT c p r m n (x 0) (x 1) (x 2) =
        Season.sweepT e p r m n (x 0) (x 1) (x 2) :=
    sweep c e p r m n _ _ _ h₁ h₂
  rw [IssuedMaxwell.TriangleCalibration.graph, IssuedMaxwell.TriangleCalibration.graph]
  simp only [Rose.numeric, Rose.aT, Rose.wave, eq]

end IssuedBridge.PostedTriangleCutReturns
