import YM.Integration.WilsonPositionHomogeneousPanel

/-! The actual joint compact test on the microscopic Wilson grid at a fixed physical radius.
Its full cell weights retain independent child residues before either continuum limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPhysicalCellTest
open Function Set Filter MeasureTheory Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Finset Source FVA2 FVA2.Register RG12 Cells Push.GridApprox XSpace.Structure1 WilsonPositionSeparatedProfileMatching
open WilsonPositionHomogeneousPanel
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable {n : ℕ} (φ : Test n) (r : ℝ) (z : UVIndex)

abbrev Sites (R : Run G) (z : UVIndex) (n : ℕ) := Fin n → Site (R.family.side z.1 z.2)

def site (x : Points n) : Sites R z n := wrap _ ∘ address (R.family.S.a z.1) (r • x)
def cell (u : Sites R z n) : Set (Points n) := (site r z) ⁻¹' {u}
def mass (u : Sites R z n) : ℂ := ∫ x in cell r z u, φ x

private theorem visible (u : Sites R z n) : MeasurableSet (cell r z u) := by
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  let U : Set (Fin n → Cover) := {c | wrap _ ∘ c=u}
  exact (Set.to_countable U).measurableSet.preimage (grid.comp (continuous_const_smul r).measurable)

private theorem integrate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : Sites R z n → Points n → E) (finite : ∀ u, Integrable (h u)) :
    (∫ x, h (site r z x) x) = ∑ u, ∫ x in cell r z u, h u x := by
  have partition (x : Points n) : h (site r z x) x = ∑ u, (cell r z u).indicator (h u) x := by
    simp [Set.indicator_apply,cell]
  have paid (u : Sites R z n) := (finite u).indicator (visible r z u)
  simp_rw [partition]
  rw [integral_finsetSum _ (fun u _=>paid u)]
  exact Finset.sum_congr rfl fun u _=>integral_indicator (visible r z u) ..

theorem total_variation :
    ∑ u : Sites R z n, ‖mass φ r z u‖ ≤ ∫ x, ‖φ x‖ := by
  have paid : Integrable (fun x : Points n=>‖φ x‖) := (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  rw [integrate r z (fun _ x=>‖φ x‖) (fun _=>paid)]
  exact Finset.sum_le_sum (fun u _=>norm_integral_le_integral_norm _)

theorem panel (d : ℕ) (w : UVIndex → Fin n → R.family.label d) :
    WilsonPositionHomogeneousPanel.panel d φ r w z =
      ∑ u : Sites R z n, mass φ r z u * R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) u (w z) := by
  let g (u : Sites R z n) := R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) u (w z)
  change (∫ x, φ x*g (site r z x)) = _
  rw [integrate r z (fun u x=>φ x*g u)
    (fun u=>(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const (g u))]
  exact Finset.sum_congr rfl (fun u _=>integral_mul_const _ _)

variable (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    (d : ℕ) (v : Tags G d n) {r : ℝ} (hr : 0<r) (c : Fin n → R.family.label d)
    (filed : ∀ i, S.project d (c i) = field F J Z d v r i)

include filed in
/-- The original UV limit is taken first on each admitted period. This uses fixed representatives
of the measured fields at the submitted real radius. -/
theorem ordered :
    f.limits (fun p=>suitable R.family.S p (dilate hr φ))
      (fun N p=>(R.family.S.a N : ℂ)^(4*n)*∑ u : Sites R (N,p) n,
        dilate hr φ (Extraction.Order.cells R.family N p u) *
          R.family.ensemble (N:=N) (p:=p) (fun _=>d) u c)
      (observed Z F J none d φ v r) := by
  have hear : S.integralOn (fun _=>d) c (dilate hr φ)=observed Z F J none d φ v r := by
    unfold Table.integralOn
    rw [zoom_integral]
    apply φ.apply_eq
    intro x hx
    change S.value (fun _=>d) (r • x) c=S.classMoment S (fun _ =>d) (r • x) (field F J Z d v r)
    rw [show field F J Z d v r = fun i=>S.project d (c i) from funext (fun i=>(filed i).symm)]
    exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl)
      (Work.A05.smul_conf hr hx) (fun i=>⟨d,c i⟩)).symm
  rw [←hear]
  exact Extraction.Order.full_read f R.family S F.room.ordered n (fun _=>d) c (dilate hr φ)

end YM.Integration.WilsonPositionPhysicalCellTest
