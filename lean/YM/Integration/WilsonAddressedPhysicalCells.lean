import YM.Extraction.Round
import YM.Euclid.Test

/-! Joint masses on the actual finite physical grid, for arbitrary finite arity and independent spatial residues. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPhysicalCells
open Function Set MeasureTheory Lattice Extraction
open scoped Classical BigOperators Topology
variable {n:ℕ} (φ:Test n) (a r:ℝ) (side:Side)

abbrev Sites (side:Side)(n:ℕ):=Fin n→Site side

def atSite (x:Points n):Sites side n:=wrap side ∘ address a (r • x)

def cell (u:Sites side n):Set (Points n):=(atSite a r side) ⁻¹' {u}

def mass (u:Sites side n):ℂ:=∫x in cell a r side u,φ x

private theorem visible (pos:0<a) (u:Sites side n):MeasurableSet (cell a r side u):=by
  have grid:Measurable (address a:Points n→Fin n→Cover):=by
    apply measurable_to_countable
    intro x
    exact measurable_segment pos (address a x)
  let U:Set (Fin n→Cover):={c|wrap side ∘ c=u}
  exact (Set.to_countable U).measurableSet.preimage (grid.comp (continuous_const_smul r).measurable)

theorem integrate {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (pos:0<a)
    (h:Sites side n→Points n→E) (finite:∀u,Integrable (h u)):
    (∫x,h (atSite a r side x) x)=∑u,∫x in cell a r side u,h u x:=by
  have partition (x:Points n):h (atSite a r side x) x=
      ∑u,(cell a r side u).indicator (h u) x:=by simp [Set.indicator_apply,cell]
  have paid u:= (finite u).indicator (visible a r side pos u)
  simp_rw [partition]
  rw [integral_finsetSum _ (fun u _=>paid u)]
  exact Finset.sum_congr rfl fun u _=>integral_indicator (visible a r side pos u) ..

theorem total (pos:0<a):(∑u:Sites side n,‖mass φ a r side u‖)≤∫x,‖φ x‖:=by
  have paid:Integrable (fun x:Points n=>‖φ x‖):=(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  rw [integrate a r side pos (fun _ x=>‖φ x‖) (fun _=>paid)]
  exact Finset.sum_le_sum (fun u _=>norm_integral_le_integral_norm _)

end YM.Integration.WilsonAddressedPhysicalCells
end
