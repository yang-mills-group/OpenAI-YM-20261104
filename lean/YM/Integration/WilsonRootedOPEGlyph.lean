import YM.Integration.WilsonMacroscopicRichOriginalFilm
import YM.Integration.WilsonRootedOPEColumn
import YM.Integration.ActualOriginalQCharges

/-! A positive preperiod native path-and-color row for every actual calibrated OPE glyph. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEGlyph
open Function Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges ActualRunCurvaturePackets NativeCurvatureTensor
open scoped BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (u : V→MS.Rake.Label B)

def mass (z : Row (R:=R) u) : ℝ :=
  tensorMass u z * ‖MvPolynomial.coeff z.2.2.val ((ofRun R (degree u z.1)).data.shape z.2.1)‖ * ‖coordinates (R:=R) u z.1 z.2.1‖

omit [DecidableEq V] [Fintype V] in
theorem mass_nonneg (z : Row (R:=R) u) : 0 ≤ mass R u z :=
  mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _=>norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

omit [DecidableEq V] [Fintype V] in
theorem issued (s : Slot u) : ∃ z : Row (R:=R) u,z.1=s ∧ 0 < mass R u z := by
  obtain ⟨i,coord,_,_⟩ := WilsonMacroscopicRichOriginalFilm.original R B s.2.size s.2.grade s.2.2.2
  obtain ⟨m,j,nonzero⟩ := WilsonRootedOPEColumn.occupied (ofRun R s.2.size) (R.makes.sections _) (ActualRunGradedKernels.section_valuation R _) i
  let z : Row (R:=R) u := ⟨s,i,m⟩
  have color : 0<tensorMass u z := (norm_pos_iff.mpr nonzero).trans_le (Finset.single_le_sum (fun t (_:t∈Finset.univ)=>norm_nonneg (coefficient (fun k=>(word m.val k).2) t)) (Finset.mem_univ j))
  have shape : MvPolynomial.coeff m.val ((ofRun R s.2.size).data.shape i)≠0 := MvPolynomial.mem_support_iff.mp m.property
  refine ⟨z,rfl,mul_pos (mul_pos color (norm_pos_iff.mpr shape)) (norm_pos_iff.mpr coord)⟩

noncomputable def row (s : Slot u) := (issued R u s).choose

omit [DecidableEq V] [Fintype V] in
theorem acquired (s : Slot u) : (row R u s).1=s ∧ 0 < mass R u (row R u s) := (issued R u s).choose_spec

def wallet : ℝ := (1+∑s : Slot u,(mass R u (row R u s))⁻¹)^Fintype.card (Slot u)

end YM.Integration.WilsonRootedOPEGlyph
