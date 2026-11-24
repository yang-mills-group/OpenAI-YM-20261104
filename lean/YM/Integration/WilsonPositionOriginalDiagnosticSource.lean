import YM.Integration.WilsonPositionOriginalDiagnosticPanel
import YM.Integration.ActualRunFullPages

/-! The diagnostic fields share the original forced pages. At their age of birth,
the normalized bare operands are exactly those of the eventually filed signed rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticSource
open Function Filter Finset Lattice Wilson RG Source Marker Extra.Multi Push FVA1
open MergeProof MergeProof.Accent MergeProof.Replicums Planned.GuardedAtom Push.GridApprox.Nil
open RG12 RG05Readout Address Native Extra.Histories MergeProof.Ribbons PhysicalNext.Repeat.Legato
open MS MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Studio MS.Local.Physical MS.Menus MS.Lifting MS.Theater Maxwell Maxwell.Free XSpace.Normalize
open ActualRunUnmaskedPartners WilsonPositionOriginalDiagnosticPanel
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (B:Deck G) {H:ℕ} {I:Type} [DecidableEq I] [Fintype I]
variable {m N per:ℕ}

theorem homogeneous (a:Glyph B H) (o:Site (R.family.side m per)) (U:Config G (R.family.side m per)) :
    ActualRunPhysicalPages.kernel R N per m a.size (entry R B a) o U =
    ((((R.family.path.rep N per m).p.threshold)⁻¹ ^ a.grade : ℝ):ℂ) *
     (((ActualOriginalDictionary.dictionary R B).cylinder a.size a.grade a.2.2).O _ o U:ℂ) := by
  rw [original_field R B]
  change (R.family.localSection a.size).places ((R.family.labels.level a.size).scaled _
    ((R.family.labels.level a.size).coords (ActualOriginalDictionary.filmLabel B a.size a.grade a.2.2))) o U=_
  rw [(R.family.labels.level a.size).scaled_pure _ (a.size,a.grade) (filmW (h:=a.size) B a.2.2).2]
  unfold Source.SectionData.places Source.SectionData.evaluate
  rw [map_smul, map_smul]
  rfl

theorem fresh (simple:G.Simple) (age:entrance R B H ≤ m) (live:m≤N)
    (a:I→Glyph B H) (o:Positions I (R.family.side m per)) (U:Config G (R.family.side m per)) :
    essence (ActualRunFullPages.pages R simple N per m live o (fun i=>(a i).size) (fun i=>entry R B (a i)))
      (fun _=>0) (fun _=>1) U = ((R.family.path.rep N per m).eval U:ℂ) • Poly.pass
      (Mach (Replicum.Bud I) (fun i=> ((((R.family.path.rep N per m).p.threshold)⁻¹ ^ (a i).grade:ℝ):ℂ) *
          (((ActualOriginalDictionary.dictionary R B).cylinder (a i).size (a i).grade (a i).2.2).O _ (o.origin i) U:ℂ))) := by
  rw [ActualRunFullPages.essence_full R simple N per m live o _ _
    (fun i=>(le_sup (s:=univ) (f:=fun j:Glyph B H=>R.family.ref j.size) (mem_univ (a i))).trans age)]
  unfold fullInput actualLog
  simp_rw [homogeneous R B]

/-- Install the inverse-normalized microscopic source, with a common original
ultraviolet and period, before propagating any subset to its reporting station. -/
theorem ultraviolet (simple:G.Simple) (age:entrance R B H ≤ m) (live:m≤N)
    (a:I→Glyph B H) (o:Positions I (R.family.side N per)) (U:Config G (R.family.side N per)) :
    essence (ActualRunFullPages.pages R simple N per N le_rfl o (fun i=>(a i).size)
      (fun i=>WilsonReportingFactorySingleton.upper R.makes (a i).size m N per (entry R B (a i))))
      (fun _=>0) (fun _=>1) U = ((R.family.path.rep N per N).eval U:ℂ) • Poly.pass
      (Mach (Replicum.Bud I) (fun i=>(R.family.S.a N:ℂ)^(a i).size *
        R.family.O N per (atK R.family R.makes (a i).size m (N,per) (entry R B (a i))) (o.origin i) U)) := by
  rw [ActualRunFullPages.essence_full R simple N per N le_rfl o _ _ (fun i=>
    ((le_sup (s:=univ) (f:=fun j:Glyph B H=>R.family.ref j.size) (mem_univ (a i))).trans age).trans live)]
  unfold fullInput
  rw [actual_log_physical R N per N o _ _ le_rfl U]
  apply congrArg (fun f:I→ℂ=>((R.family.path.rep N per N).eval U:ℂ) • Poly.pass (Mach (Replicum.Bud I) f))
  funext i
  have t := (R.family.factory (a i).size N per).terminal.apply_symm_apply
    (atK R.family R.makes (a i).size m (N,per) (entry R B (a i)))
  exact congrArg (fun v=>(R.family.S.a N:ℂ)^(a i).size * R.family.O N per v (o.origin i) U) t

end YM.Integration.WilsonPositionOriginalDiagnosticSource
