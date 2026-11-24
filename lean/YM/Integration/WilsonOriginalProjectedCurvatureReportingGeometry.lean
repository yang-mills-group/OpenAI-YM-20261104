import YM.Integration.WilsonOriginalProjectedCurvatureReportingClock

/-! A single prospective exponential bound on the acquired support exponent
finances every fixed, subsequently registered set of lifted Wilson paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureReportingGeometry
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureEnvelope
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open scoped Classical BigOperators
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (J:Request V) (u:V→MS.Rake.Label B) (extra:V→ℕ) (w:V→ℝ)
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u

def length (s:Rows):ℝ:=2*ActualOriginalQCharges.rowFall u s+(liftHeight D₁ u s extra:ℝ)
def salary (s:Rows):ℝ:=Poly.toll w ((Stock.census V).fire s.1.1)*ActualOriginalQCharges.rowMass D₁ u s

theorem bought {σ x:ℝ} {y:ℕ}
    (reach:(∑ s:Rows,|length R J u extra s|)≤(y:ℝ)+1)
    (prepaid:Real.exp (((y:ℝ)+1)*|σ|)≤x) :
    WilsonOriginalProjectedCurvatureClock.charge R J u σ σ extra w ≤
      (∑ s:Rows,|salary R J u w s|)*x := by
  rw [WilsonOriginalProjectedCurvatureClock.charge,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  have row:|length R J u extra s|≤(y:ℝ)+1:=
    (Finset.single_le_sum (f:=fun s:Rows=>|length R J u extra s|)
      (fun i _=>abs_nonneg _) (Finset.mem_univ s)).trans reach
  have paid:Real.exp (σ*length R J u extra s)≤x:=calc
    _ ≤ Real.exp (abs σ * abs (length R J u extra s)) := Real.exp_le_exp.mpr (by rw [←abs_mul]; exact le_abs_self _)
    _ ≤ Real.exp (((y:ℝ)+1)*|σ|) := Real.exp_le_exp.mpr (by rw [mul_comm ((y:ℝ)+1)]; exact mul_le_mul_of_nonneg_left row (abs_nonneg _))
    _ ≤ x := prepaid
  calc
    ActualOriginalQCharges.rowPrice D₁ u w (σ+σ) s*Real.exp (σ*(liftHeight D₁ u s extra:ℝ)) =
        salary R J u w s*Real.exp (σ*length R J u extra s):=by
      unfold ActualOriginalQCharges.rowPrice salary length
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ abs (salary R J u w s) * Real.exp (σ*length R J u extra s) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ abs (salary R J u w s) * x :=mul_le_mul_of_nonneg_left paid (abs_nonneg _)

omit [DecidableEq V] in
theorem eventual :
    ∀ᶠ m:ℕ in atTop, (∑s:Rows,|length R J u extra s|)≤(R.alloy.B.a.clock.J m:ℝ)+1 := by
  obtain ⟨n,hn⟩:=exists_nat_gt (∑s:Rows,|length R J u extra s|)
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop n] with m hm
  have elevated:(n:ℝ)≤(R.alloy.B.a.clock.J m:ℝ):=by exact_mod_cast hm
  linarith

end YM.Integration.WilsonOriginalProjectedCurvatureReportingGeometry
