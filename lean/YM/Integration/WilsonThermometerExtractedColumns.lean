import YM.Frontier6.Multi.Seams.Shift
import YM.Next.EXTRACTION.Basis
import YM.Extraction.Inherited

/-! Every measured reference vector is charged at its own current value
on the original terminal extraction, before the volume limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerExtractedColumns
open Function Set Filter Cells Extraction Wilson Lattice
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} (makes : C.Makes) (room : CellHyp C f)
include makes room

theorem original (d : ℕ) : ∃ k₀ : ℕ, ∃ A : ℝ, 0≤A ∧ ∀ k≥k₀,
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ hk : k≤z.1, ∀ (m : ℕ) (early:m≤k) (j:Site (C.side m z.2))
      (o : Site (C.side z.1 z.2)) (v:C.label d),
      let T:=center C.S z.2 (early.trans hk) 0
      o ∈ T.margin j (3*span C.S hk z.2) →
      ∃ Y, Interior (T.chamber 0) Y ∧
        T.rootTest (C.beta z.1 z.2) Y ≤ (A*C.S.a k^(-(d:ℝ)-1)+1)*(1+‖v‖) ∧
        T.copy j Y = C.O z.1 z.2 v o := by
  obtain ⟨k₀,_,A,positive,priced⟩ := room.centered d 1 1 zero_lt_one zero_lt_one
  refine ⟨k₀,A,positive,fun k age=>?_⟩
  rw [Extraction.Order.fused]
  apply (priced k age 1 zero_lt_one).mono
  intro N period
  apply period.mono
  rintro p ⟨hk,bank⟩
  refine ⟨hk,?_⟩
  intro m early j o v T inside
  let B:=1+‖v‖
  have bpos:0<B:=by dsimp [B]; positivity
  have one: (B:ℂ)≠0:= Complex.ofReal_ne_zero.mpr bpos.ne'
  let u:C.label d:=((B:ℂ)⁻¹) • v
  have uv : (B:ℂ) • u=v := by simp [u,smul_smul,one]
  have bounded : ‖u‖≤1 := by
    rw [show ‖u‖ = ‖v‖/B by simp [u,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos bpos,
      div_eq_inv_mul]]
    exact (div_le_one bpos).mpr (by dsimp [B]; linarith)
  have physical : C.O (f.mesh p) (f.per N) v 0 = (B:ℂ) • C.O (f.mesh p) (f.per N) u 0 := by
    have l := ((C.linearO (f.mesh p) (f.per N) d 0).mk' _).map_smul (B:ℂ) u
    change C.O (f.mesh p) (f.per N) ((B:ℂ) • u) 0 = (B:ℂ) • C.O (f.mesh p) (f.per N) u 0 at l
    rwa [uv] at l
  obtain ⟨localU,charge⟩ := bank u bounded 0
  let S:=center C.S (f.per N) hk 0
  have placed : Interior (S.chamber 0) (C.O (f.mesh p) (f.per N) v 0) := by
    rw [physical]; exact localU.scale _
  have price : S.rootTest (C.beta (f.mesh p) (f.per N)) (C.O (f.mesh p) (f.per N) v 0) ≤
      (A*C.S.a k^(-(d:ℝ)-1)+1)*B := by
    rw [physical,Next.Extract.root_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos bpos,mul_comm _ B]
    exact mul_le_mul_of_nonneg_left charge bpos.le
  obtain ⟨Y,legal,paid,det⟩ := Frontier6.Platform.moved_basis makes hk early j placed price inside
  refine ⟨Y,legal,paid,det.trans ?_⟩
  funext U
  change C.O (f.mesh p) (f.per N) v 0 (Lattice.translate o U) = _
  rw [C.translation,zero_add]

end YM.Integration.WilsonThermometerExtractedColumns
