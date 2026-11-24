import YM.Integration.WilsonOriginalTwoFlatIRPoolMesh

/-! The signed compact booking and its literal continuum quadrature locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolRound
open Function Filter Finset Set Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox WilsonPositionThermometerReading
open WilsonThermometerUnitFilingFourSquare
open WilsonCenteredCompactBooking (cell site mass measurable_cell)
open WilsonCenteredPhysicalPanel (Sites)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G)

def rounded {n:ℕ}(r:ℝ)(f:ℕ)(x:Points n):Points n:=
  r⁻¹ • tag (R.family.S.a f) (address (R.family.S.a f) (r • x))

theorem near {n f:ℕ}(φ:Test n){r τ:ℝ}(rp:0<r)(size:4*(n:ℝ)*R.family.S.a f≤τ*r)
    {x:Points n}(hit:φ x≠0):rounded R r f x∈cthickening τ (tsupport (φ:Points n→ℂ)):=by
  let y:=rounded R r f x
  have actual:r • y=tag (R.family.S.a f) (address (R.family.S.a f) (r • x)):=by
    simp [y,rounded,smul_smul,rp.ne']
  have err:=Extraction.approximate (R.family.S.a_pos f) (r • x)
  have scale:dist (r • y) (r • x)=r*dist y x:=by
    rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,dist_eq_norm]
  have fee:dist y x≤τ:=(mul_le_mul_iff_right₀ rp).mp (by
    rw [←scale,actual];exact err.trans (size.trans_eq (mul_comm _ _)))
  exact mem_cthickening_of_dist_le _ x τ _ (subset_tsupport _ hit) fee

theorem placement {n f N:ℕ}(r:ℝ)(rp:0<r)(live:f≤N)(per:ℕ)(x:Points n)(i:Fin n):
    wrap (R.family.side N per) (address (R.family.S.a N) (r • rounded R r f x) i)=
    (R.family.S.toDepth live per).embed (site R r (f,per) x i):=by
  have actual:r • rounded R r f x=tag (R.family.S.a f) (address (R.family.S.a f) (r • x)):=by
    simp [rounded,smul_smul,rp.ne']
  rw [actual]
  exact WilsonReflectedPublicAlignedPoints.grid R live per _ i

theorem field {n:ℕ}(r:ℝ)(f:ℕ)(F₀:Points n→ℂ):Measurable (fun x:Points n=>F₀ (rounded R r f x)):=by
  have grid:Measurable (address (R.family.S.a f):Points n→(Fin n→ Cover)):=by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos f) (address (R.family.S.a f) x)
  exact (measurable_of_countable (fun o:Fin n→ Cover=>F₀ (r⁻¹ • tag (R.family.S.a f) o))).comp
    (grid.comp (continuous_const_smul r).measurable)

theorem weighted {n:ℕ}(φ:Test n)(r:ℝ)(z:ℕ×ℕ)(q:Sites R z n→ℂ):
    signed R φ r z (fun o=>q o.val)=∫x,φ x*q (site R r z x):=by
  let occupied:=cells R φ r z
  let load:=fun o:Sites R z n=>mass R φ r z o*q o
  have stored:(∑o:occupied,load o.val)=∑o∈occupied,load o:=by
    simpa only [Finset.attach_eq_univ] using (Finset.sum_attach occupied load)
  have whole:(∑o∈occupied,load o)=∑o,load o:=by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro o _ miss
    have zero:mass R φ r z o=0:=by
      by_contra h
      exact miss (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    simp [load,zero]
  change (∑o:occupied,load o.val)=_
  rw [stored,whole]
  have split(x:Points n):φ x*q (site R r z x)=∑o,(cell R r z o).indicator (fun y=>φ y*q o) x:=by
    simp [Set.indicator_apply,cell]
  simp_rw [split]
  rw [integral_finsetSum _ (fun o _=>((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const
    (q o)).indicator (measurable_cell R r z o))]
  apply sum_congr rfl
  intro o _
  rw [integral_indicator (measurable_cell R r z o),integral_mul_const]
  rfl

end YM.Integration.WilsonOriginalTwoFlatIRPoolRound
end
