import YM.Integration.WilsonMatrixOriginalDeckReturn
import YM.RG17.Gathers

/-! The full mixed spatial measurement as a limit of the original finite Wilson moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRegulated
open Filter Set MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Extraction.Order Table Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} {R:Run G} (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Both external physical fields are chosen at their respective radii before the regulator. -/
def arms (r s:ℝ) (a b:Glyph B h) : Fin 2 → S.Field h :=
  ![J r h (WilsonMatrixOriginalDeckColumns.basis R.family B h a),
    J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h b)]

/-- Each entry integrates the complete product under the original lattice Wilson law. -/
def reading (g:Test 2) {r:ℝ} (hr:0<r) (x:(ℕ×ℕ)→Fin 2→R.family.label h) (z:ℕ×ℕ) : ℂ :=
  smears R.family z.1 z.2 (fun i=>⟨h,x z i⟩) (dilate hr g)

include F in
/-- The original hierarchy compares the whole smeared Wilson reading to the mixed physical frame. -/
theorem measured (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (a b:Glyph B h)
    (u:Filter (ℕ×ℕ)) [u.NeBot] (per:u≤f.fuse) (x:(ℕ×ℕ)→Fin 2→R.family.label h)
    (v:Fin 2→R.family.label h) (tends:∀i,Tendsto (fun z=>x z i) u (𝓝 (v i)))
    (filed:∀i,S.project h (v i)=arms (R:=R) B J h r s a b i) :
    Tendsto (reading (R:=R) h g hr x) u (𝓝 (WilsonMatrixOriginalDeckMixed.mixed B J h g r s a b)) := by
  have tested := calibrated_smear (d:=fun _:Fin 2=>h) F.room.ordered u per (dilate hr g) tends
  suffices value : S.integralOn (fun _:Fin 2=>h) v (dilate hr g) =
      WilsonMatrixOriginalDeckMixed.mixed B J h g r s a b by
    rw [←value]
    exact tested
  change (dilate hr g).applyTo (fun y=>S.value (fun _:Fin 2=>h) y v) = _
  rw [zoom_integral]
  apply g.apply_eq
  intro y hy
  have same := S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 2=>h)
    (Work.A05.smul_conf hr hy) v
  rw [show (fun i:Fin 2=>S.project h (v i))=arms (R:=R) B J h r s a b from funext filed] at same
  exact same.symm

include F in
/-- Both nominated continuum labels have genuine finite original representatives at each height. -/
theorem pinned (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (a b:Glyph B h)
    (u:Filter (ℕ×ℕ)) [u.NeBot] (per:u≤f.fuse) :
    Tendsto (reading (R:=R) h g hr (fun _ i=>S.representative h (arms (R:=R) B J h r s a b i))) u
      (𝓝 (WilsonMatrixOriginalDeckMixed.mixed B J h g r s a b)) := by
  exact measured B F J h g hr s a b u per _ _ (fun _=>tendsto_const_nhds) (fun _=>S.rep _ _)

end YM.Integration.WilsonMatrixOriginalDeckRegulated
