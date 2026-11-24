import YM.RG12.Canonical.Basis
import YM.RG12.Canonical.Stops
import YM.RG12.Canonical.Low
import YM.OPE.Logarithmic

/-! # Endpoint conditional on *comparable-radius* physical matrix estimates -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Finset Lattice RG Source Frames Table OPE
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} (B : DiffPlan S)
  {M : ∀ d, ℕ → RepChart C d} {φ : Extraction.Order}
  (U : Spec.Final C φ S)

/-- For each horizon separately, never asks for a cumulative matrix comparison.
 Use any qualified filter after observing full field columns at ALL k.
 Can replace reference P with a preferred formal calibration (put both that P and the actual
 Y frames on the same Filtration flag, see Desk.compatible for one adapter).
 This does not specify the tests themselves: use in the `LogTrace` consumer by verifying the
 bounds on R for actual test geometries in S.Field (unselected), not a comparison on a
 different physical construction. In Consecutive, readings must extend to both
 `Sample.length age` and the neighboring length (testing the same bigger-age pivot basis and
 the specified shear); in ReadingAt both clauses are at `Sample.length (Sample.atMesh C k)`
 which brackets the actual mesh k within a constant ratio (see Stops proof). Can enlarge those
 requirements as in other OPE producers, but don't need general contact or degenerating
 geometries or even multiple fields for this matrix input. -/
def FramesInput (Q:Prescription B) (hq:Q.Coherent)
    (M: ∀ d,ℕ → RepChart C d) (d : ℕ) :=
  let V:= Desk.Sector B d; let m:= Sample.atMesh C
  ∃ (Y : ℕ → Col V →ₗ[ℂ] S.Field d)(R:ℕ → S.Field d → ℝ)(J:ℕ → Col V ≃ₗ[ℂ] Col V)
    (K:ℝ)(p b n₀:ℕ),
    Consecutive Sample.age Sample.length Sample.ratio Y (Desk.official Q hq d) R J K p b n₀ ∧
      ∃ (Z:ℕ→ Col V →ₗ[ℂ] C.label d) (e:ℕ), ∀ᶠ k in atTop,
        Nonempty (ReadingAt C S d V (R (m k)) k M (Z k) (e+2))

local notation "B0" => U.sector.derivatives
variable (hG:G.Simple)
include hG

lemma close_matrices (hC:C.Makes) (Q:Prescription B0)(hq:Q.Coherent) (h:∀ (F:Filter UVIndex) [F.NeBot], F ≤ φ.fuse → ∀ M,
    Observing C hC F M → ∀ d,4 ≤ d→ FramesInput B0 Q hq M d):
    ∃ F:Filter UVIndex,F.NeBot ∧ F≤ φ.fuse∧ OPE.Log.MatrixTicket (C:=C) S B0 F := by
  refine matrix_ticket_from_limits hG S B0 _ hC (fun F _ hF M hm=> ?_)
  suffices ht : ∀ d:ℕ, RightPrice C S M d ∧ ∀ w, RowPrice C S B0 M d w from
    ⟨fun i=> (ht i).1,fun i=> (ht i).2⟩
  intro i; rcases lt_or_ge i 4 with he|he
  · exact ⟨low_right_price hG hm S i he,fun w=> low_row_price hG hm S B0 U.room.kernel.laws U.phase.transport.injection i w he⟩
  obtain ⟨Y,R,J,K,p,b,n,hV,Z,e,hZ⟩:= h F hF _ hm i he
  have ht:= Sample.enough_stops C hG e n
  exact ⟨march_right hV (Sample.atMesh C) ht Z hZ hG,fun w=> march_row hV (Sample.atMesh C) ht Z hZ hG w (fun j _ x=> Desk.fits Q hq i j x)⟩

theorem sharp_from_measurements (L:Facilities C φ S) (Q:Prescription B0)(hq:Q.Coherent)
    (h:∀ (F:Filter UVIndex) [F.NeBot], F ≤ φ.fuse → ∀ M,
      Observing C U.room.cutoff F M → ∀ d,4 ≤ d → FramesInput B0 Q hq M d) : LogTrace U Q := by
  obtain ⟨b,_,hb,hV⟩:= close_matrices U hG U.room.cutoff Q hq h
  exact OPE.tickets_suffice U L hb hV hq
end YM.RG12
