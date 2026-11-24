import YM.Integration.WilsonMovingChildLease
import YM.Push.GRID_APPROXIMATION.Translate

/-! An entire signed child at the true fine offset under each physical
site reflection. Its inner-cell replication price is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingChildReflection
open Function Set Lattice Cells Wilson RG Labels Source Push Push.GridApprox Extraction
open Next.Extract MergeProof WilsonOffsetReportingProducts
open scoped Classical
variable {G : Gauge}

theorem place (C : Family G) {d : ℕ} (V : SectionData (C.labels.level d)) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (b : Presentation C) (x : C.label d) (o : Site (C.side N p)) :
    corrected C V N p P b x 0 ∘ Lattice.translate o = corrected C V N p P b x o := by
  change (C.O N p (b.step d (N,p) x) 0 ∘ Lattice.translate o) +
    (residual C V N p P (x-b.step d (N,p) x) 0 ∘ Lattice.translate o) = _
  rw [WilsonOffsetPrimaryLease.place,WilsonOffsetDiscrepancyLease.place]; rfl

def before {n : Side} (T : Tiling n) (i : T.Cell) (x : Site n) := (T.omega i)⁻¹.act (T.copyMap i x)

theorem moved {n : Side} (T : Tiling n) (i : T.Cell) (x : Site n) (Z : Site n → Config G n → ℂ)
    (born : ∀ o, Z 0 ∘ Lattice.translate o = Z o) :
    Z (before T i x) ∘ pull (T.omega i) 0 = Z x ∘ pull (T.omega i) (T.translateBy i) := by
  funext U; change Z (before T i x) _ = Z x _
  rw [← congrFun (born (before T i x)) _,← congrFun (born x) _]
  simp only [Function.comp_apply,← pull_one,pull_pull,mul_one,affine,add_zero,before,
    Signed.act_inv,Tiling.copyMap]

private theorem chamber (S : Schedule) {j N p : ℕ} (h : j ≤ N) (s : Signed) :
    MapsTo (affine (R:=Per (S.side N p)) s 0) ((tilesAt S p h).chamber 0) ((tilesAt S p h).chamber 0) := by
  rw [tiling_window]
  change MapsTo _ (window (anchor S p h (0:Site (S.side j p))) _) (window (anchor S p h (0:Site (S.side j p))) _)
  rw [show anchor S p h 0 = 0 from (S.toDepth h p).root.map_zero]
  simpa only [affine,Signed.act_zero,zero_add] using
    window_affine (n:=S.side N p) (r:=(S.toDepth h p).count.val/2) 0 0 s

theorem reflected (S : Schedule) {j N p : ℕ} (h : j ≤ N) (β w M : ℝ)
    (T : Tiling (S.side N p)) (i : T.Cell) (x : Site (S.side N p)) (v : Site (S.side j p))
    (Z : Site (S.side N p) → Config G (S.side N p) → ℂ) (born : ∀ o, Z 0 ∘ Lattice.translate o = Z o)
    (paid : ∃ X, Interior ((tilesAt S p h).chamber 0) X ∧ w*(tilesAt S p h).rootTest β X ≤ M ∧
      (tilesAt S p h).copy v X = Z (before T i x)) :
    ∃ Y, Interior ((tilesAt S p h).chamber 0) Y ∧ w*(tilesAt S p h).rootTest β Y ≤ M ∧
      (tilesAt S p h).copy ((T.omega i).act v) Y = T.copy i (Z x) := by
  obtain ⟨X,inside,cost,equation⟩ := paid
  let U := tilesAt S p h
  let s := T.omega i
  let Y := X ∘ pull s 0
  have hi : Interior (U.chamber 0) Y := inside.unchanged s 0 (chamber S h s)
  have hr : U.rootTest β Y = U.rootTest β X := root_oriented S h β s X inside
  have eq : U.copy (s.act v) Y = Z x ∘ pull s (T.translateBy i) := (copy_oriented S h v s X).trans
    ((congrArg (fun z : Config G (S.side N p) → ℂ => z ∘ pull s 0) equation).trans (moved T i x Z born))
  by_cases rev : T.hand i
  · refine ⟨fun a => star (Y a),hi.real,?_,?_⟩
    · rw [Work.B15.rootTest_star,hr]; exact cost
    · funext a
      have he : U.copy (s.act v) (fun b => star (Y b)) a = star (U.copy (s.act v) Y a) := by
        unfold Tiling.copy; split <;> rfl
      rw [he,eq]; simp only [Function.comp_apply,Tiling.copy,if_pos rev,s]
  · refine ⟨Y,hi,?_,?_⟩
    · rw [hr]; exact cost
    · rw [eq]; funext a; simp only [Function.comp_apply,Tiling.copy,if_neg rev,s]

end YM.Integration.WilsonMovingChildReflection
