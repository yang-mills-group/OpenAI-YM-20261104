import YM.Integration.WilsonPositionProgramPublicMicroscopic

/-! The measured matrix of one finite preframe. The same coefficients weight
its actual microscopic basis arms and every cell of each determining test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicFiniteMatrix
open Function Set Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedPivot WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramPublicMicroscopic WilsonPositionProgramPublicGram
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {d : ℕ} (B : Profiles R d) {r : ℝ} (hr : 0 < r)
    {I : Type*} [Fintype I] (basis : Module.Basis I ℂ ((Bel R.family.book).Field d))

def measured (labels : I → ℕ×ℕ → R.family.label d) (z : ℕ×ℕ) :
    (Bel R.family.book).Field d →ₗ[ℂ] (B.probes.index → ℂ) :=
  basis.constr ℂ (fun j => sheet F J Z B hr z (labels j z))

omit [Fintype I] in
theorem entry (labels : I → ℕ×ℕ → R.family.label d) (z : ℕ×ℕ) (i : I) :
    measured F J Z B hr basis labels z (basis i) = sheet F J Z B hr z (labels i z) :=
  basis.constr_basis ℂ _ i

theorem converges {l : Filter (ℕ×ℕ)} [l.NeBot] (order : l ≤ f.fuse)
    (rows : ∀ i : I, Arm R.family S l d (homogeneous F J Z r d (basis i))) :
    Tendsto (fun z => (measured F J Z B hr basis (fun i => (rows i).source) z).toContinuousLinearMap) l
      (𝓝 (samples F J Z B r).toContinuousLinearMap) := by
  apply Dash.fit_plane
  intro x
  let P := samples F J Z B r
  let A z := measured F J Z B hr basis (fun i => (rows i).source) z
  have hit (i : I) : Tendsto (fun z => A z (basis i)) l (𝓝 (P (basis i))) := by
    simpa only [A,P,samples,LinearMap.comp_apply,LinearEquiv.coe_coe,entry] using received F J Z B hr order (rows i)
  have p (L : (Bel R.family.book).Field d →ₗ[ℂ] (B.probes.index → ℂ)) :
      L x = ∑ i, (basis.repr x i) • L (basis i) := by
    calc
      _ = L (∑ i, basis.repr x i • basis i) := congrArg L (basis.sum_repr x).symm
      _ = _ := by simp only [map_sum,map_smul]
  change Tendsto (fun z => A z x) l (𝓝 (P x))
  simp_rw [p]
  exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.smul (hit i))

end YM.Integration.WilsonPositionProgramPublicFiniteMatrix
