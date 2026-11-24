import YM.Integration.WilsonCenteredPhysicalPanel

/-! A genuine compact, independently addressed Wilson source and its original
canonical filing. Integration over the actual subcell and the original ordered
extraction are exposed with their own exact cutoff weights. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompactBooking
open Function Set MeasureTheory Table Spec Lattice Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Finset RG12 Cells Push.GridApprox Trace.Physical.GermGraph RG16 RG16.Literal
open WilsonCenteredPhysicalPanel
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n : ℕ} (caps : Fin n → ℕ) (φ : Test n) (r : ℝ) (z : UVIndex)

def site (x : Points n) : Sites R z n := wrap _ ∘ address (R.family.S.a z.1) (r • x)
def cell (u : Sites R z n) := (site R r z) ⁻¹' {u}
def mass (u : Sites R z n) : ℂ := ∫x in cell R r z u,φ x

theorem measurable_cell (u : Sites R z n) : MeasurableSet (cell R r z u) :=by
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) :=by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  let U : Set (Fin n → Cover) := {c | wrap _ ∘ c=u}
  exact (Set.to_countable U).measurableSet.preimage (grid.comp (continuous_const_smul r).measurable)

/-- The original subcell weights cost only the submitted test's total variation. -/
theorem variation : ∑u:Sites R z n,‖mass R φ r z u‖ ≤ ∫x,‖φ x‖ :=by
  have integrable : Integrable (fun x:Points n=>‖φ x‖) := (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have split (x:Points n) : ‖φ x‖=∑u:Sites R z n,(cell R r z u).indicator (fun y=>‖φ y‖) x :=by
    simp [Set.indicator_apply,cell]
  calc
    _ ≤ ∑u:Sites R z n,∫x in cell R r z u,‖φ x‖ :=
      Finset.sum_le_sum fun u _=>norm_integral_le_integral_norm _
    _ = _ :=by
      conv_rhs => rw [show (fun x=>‖φ x‖)=(fun x=>∑u:Sites R z n,(cell R r z u).indicator (fun y=>‖φ y‖) x) from funext split]
      rw [integral_finsetSum _ fun u _=>integrable.indicator (measurable_cell R r z u)]
      exact Finset.sum_congr rfl fun u _=>(integral_indicator (measurable_cell R r z u)).symm

/-- The tested field keeps the entire joint configuration at the actual subcell sites. -/
theorem exact (w : ∀j,R.family.label (caps j)) :
    R.family.omega z.1 z.2 (cylinder R caps z w (mass R φ r z)) =
      ∫x,φ x*R.family.ensemble (N:=z.1) (p:=z.2) caps (site R r z x) w :=by
  let e (u:Sites R z n) := R.family.ensemble (N:=z.1) (p:=z.2) caps u w
  have split (x:Points n): φ x*e (site R r z x)=∑u,(cell R r z u).indicator (fun y=>φ y*e u) x :=by
    simp [Set.indicator_apply,cell]
  change _=∫x,φ x*e (site R r z x)
  simp_rw [split]
  rw [WilsonCenteredPhysicalPanel.value,integral_finsetSum _ (fun u _=>((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const (e u)).indicator (measurable_cell R r z u))]
  apply sum_congr rfl
  intro u _
  rw [integral_indicator (measurable_cell R r z u),integral_mul_const]
  rfl

/-- One original book at every opened date for exactly the full compact cell source. -/
theorem filed (w : ∀j,R.family.label (caps j)) (simple : G.Simple) (out u : ℕ)
    (input : ∀j,R.t (caps j) ≤ z.1) (start : R.t out ≤ u) (stop : u ≤ z.1)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ z.1) (opened : Opened R.family out u z.2) :
    Booked R.family z.1 z.2 out (cylinder R caps z w (mass R φ r z)) u stop :=
  booked R caps z w (mass R φ r z) simple out u input start stop funded opened

/-- The original UV and volume extraction of this cylinder with its prescribed
point-cell weights, at a fixed real radius and a fixed original label tuple. -/
theorem ordered {f : Extraction.Order} {S : Table R.family.book}
    (ord : f.Ordered R.family S) (w : ∀j,R.family.label (caps j)) (hr : 0 < r) :
    f.limits (fun p=>suitable R.family.S p (dilate hr φ))
      (fun N p=> R.family.omega N p (cylinder R caps (N,p) w (fun u=>
        (R.family.S.a N : ℂ)^(4*n)*dilate hr φ (Extraction.Order.cells R.family N p u))))
      (S.integralOn caps w (dilate hr φ)) :=by
  have original:=Extraction.Order.full_read f R.family S ord n caps w (dilate hr φ)
  have converted (N p:ℕ) : R.family.omega N p (cylinder R caps (N,p) w (fun u=>
      (R.family.S.a N:ℂ)^(4*n)*dilate hr φ (Extraction.Order.cells R.family N p u))) =
      (R.family.S.a N:ℂ)^(4*n)*∑u:Sites R (N,p) n,dilate hr φ (Extraction.Order.cells R.family N p u) *
        R.family.ensemble (N:=N) (p:=p) caps u w :=by
    rw [mul_sum]
    simpa only [mul_assoc] using WilsonCenteredPhysicalPanel.value R caps (N,p) w
      (fun u=>(R.family.S.a N:ℂ)^(4*n)*dilate hr φ (Extraction.Order.cells R.family N p u))
  simp_rw [converted]
  exact original

end YM.Integration.WilsonCenteredCompactBooking
