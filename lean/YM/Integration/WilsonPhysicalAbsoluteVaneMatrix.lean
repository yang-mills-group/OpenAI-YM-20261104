import YM.Integration.WilsonPhysicalStationMenuSalary

/-! The square matrix of actual signed weak measurements on the full regulated Wilson free
quotient, with an inverse controlled uniformly over all genuine periods and fine cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneMatrix
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalAbsoluteVaneDirections (native variation)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))

variable (Z:WilsonPrescription G)(lead:PhysMS.Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
variable {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

def cuts:Filter (ι×ℕ×ℕ):=
  Filter.comap Prod.fst u ⊓ Filter.principal {z | (books (age z.1)).W.k<z.2.1}

variable {I:Type}[Fintype I][DecidableEq I](d:Fin (D+1))(basis:Module.Basis I ℂ ((Bel R.family.book).Field d))

def filed {r:ℝ}(B:Book F (l:=l) H arch D T r)(N p:ℕ):Matrix I I ℂ:=
  LinearMap.toMatrix basis basis (((Cells.standard R.family).project d).comp
    (WilsonPhysicalAbsoluteVaneHome.read F J Z B d N p))

include shared near lead obeys in
theorem original:
    Tendsto (fun z:ι×ℕ×ℕ=>filed F J Z d basis (books (age z.1)) z.2.1 z.2.2)
      (cuts F books u age) (𝓝 1):=by
  have proj:Tendsto Prod.fst (cuts F books u age) u:=tendsto_comap.mono_left inf_le_left
  have permitted:∀ᶠz:ι×ℕ×ℕ in cuts F books u age,(books (age z.1)).W.k<z.2.1:=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  have cv (y:(Bel R.family.book).Field d):
      Tendsto (fun z:ι×ℕ×ℕ=>WilsonPhysicalAbsoluteVaneHome.read F J Z (books (age z.1)) d z.2.1 z.2.2 y)
        (cuts F books u age) (𝓝 (ladder R.family d y)):=by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    have q:=WilsonPhysicalAbsoluteVaneHome.fixed F J simple a books shared Z lead obeys u age near d y (ε/2) (half_pos ep)
    filter_upwards [proj.eventually q,permitted] with z good live
    rw [dist_eq_norm]
    exact (good z.2.1 z.2.2 live).trans_lt (half_lt_self ep)
  have exactUnit:LinearMap.toMatrix basis basis (((Cells.standard R.family).project d).comp (ladder R.family d).toLinearMap)=(1:Matrix I I ℂ):=by
    have L:((Cells.standard R.family).project d).comp (ladder R.family d).toLinearMap=LinearMap.id:=LinearMap.ext fun x=>ladder_reads x
    rw [L,LinearMap.toMatrix_id]
  rw [←exactUnit]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let test:R.family.label d→ₗ[ℂ]ℂ:=(basis.coord i).comp ((Cells.standard R.family).project d)
  have result: Tendsto (fun z:ι×ℕ×ℕ=>test (WilsonPhysicalAbsoluteVaneHome.read F J Z (books (age z.1)) d z.2.1 z.2.2 (basis j)))
      (cuts F books u age) (𝓝 (test (ladder R.family d (basis j)))):=
    test.continuous_of_finiteDimensional.continuousAt.tendsto.comp (cv (basis j))
  simp only [filed,LinearMap.toMatrix_apply,LinearMap.comp_apply,test,Module.Basis.coord_apply] at result ⊢
  convert result using 1 <;> rfl

include shared near lead obeys in
theorem reversible:
    let M:=fun z:ι×ℕ×ℕ=>filed F J Z d basis (books (age z.1)) z.2.1 z.2.2
    (∀ᶠ z in cuts F books u age,1/2<‖(M z).det‖ ∧ IsUnit (M z).det) ∧
      Tendsto (fun z=>(M z)⁻¹) (cuts F books u age) (𝓝 1):=by
  intro M
  have heard:=original F J simple a books shared Z lead obeys u age near d basis
  have center:Tendsto (fun z=>(M z).det) (cuts F books u age) (𝓝 (1:ℂ)):=by
    simpa [Function.comp_def,M] using (continuous_id.matrix_det.continuousAt.tendsto.comp heard)
  have safe:∀ᶠz in cuts F books u age,1/2<‖(M z).det‖:=by
    apply Filter.Tendsto.eventually center.norm
    simpa using (eventually_gt_nhds (a:=(1:ℝ)) (b:=1/2) (by norm_num))
  refine ⟨safe.mono (fun z h=>⟨h,isUnit_iff_ne_zero.mpr (norm_pos_iff.mp (by linarith))⟩),?_⟩
  have inverse:ContinuousAt Inv.inv (1:Matrix I I ℂ):=continuousAt_matrix_inv 1
    (by rw [Matrix.det_one,Ring.inverse_eq_inv'];exact continuousAt_inv₀ one_ne_zero)
  simpa [Function.comp_def,M] using inverse.tendsto.comp heard

end YM.Integration.WilsonPhysicalAbsoluteVaneMatrix
