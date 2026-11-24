import YM.Integration.WilsonOneFrameDetectorWindows
import YM.Next.UV_STRESS.Focus

/-! All finite compact windows needed by the derivative detector, on the
original sequence of radii with the measured homogeneous columns. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFrameFieldDerivative
open Filter Set Function Lattice Wilson RG Source OPE Spec Table Climb Ward Maxwell PhysMS Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonOneFrameFixedReadings (ruler)
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)
    (radii:Scaling S)

open Work.A04 Bid
include lead owed simple in
theorem transport (d : ℕ) : ConLap (ruler F J Z radii) F.sector.derivatives.deriv d
    (Free.scheme R.family.labels).deriv radii.r := by
  classical
  obtain ⟨s, hs⟩ := finite_faithful _ (row_faithful (Bel R.family.book) (d+1))
  obtain ⟨N, hN⟩ := (eventually_all.mpr fun i : s => eventually_ge_atTop (i.val.n+1)).exists
  have hD : ∀ᶠ D in (atTop : Filter ℕ), ∀ i : s, ∀ j, (i.val.letter j).1 ≤ D :=
    eventually_all.mpr fun _ => eventually_all.mpr fun _ => eventually_ge_atTop _
  obtain ⟨D, hd, hD⟩ := ((eventually_ge_atTop (d+1)).and hD).exists
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (eventually_all.mpr fun i : s => eventually_window i.val.clear))
  let p := ruler F J Z radii
  have pB : 0<B := zero_lt_one.trans_le (hB B le_rfl).1
  have h := WilsonOneFrameDetectorWindows.original F J Z lead owed simple radii N D 1 B pB
  unfold ConLap
  apply tendsto_pi_nhds.mpr; intro a
  apply Dash.fit_plane (fun k => ((p.r k • p.aisle k d (leaves F.sector.derivatives.deriv d)) a).toLinearMap) ((Free.scheme R.family.labels).deriv d a)
  intro v
  apply tendsto_of_fitted (fun k => LinearMap.pi fun i : s => approxRow p (d+1) i.val k) _ hs
  · intro x; refine tendsto_pi_nhds.mpr fun i => ?_
    exact tendsto_row p (table_sym _) h (hN i) hd
      (hD i) ((hB B le_rfl).2 i) x
  refine tendsto_pi_nhds.mpr fun i => ?_
  exact tendsto_deriv_row F.room.kernel F.sector.derivatives (spectate_evolution F none) (table_sym _) (Free.scheme R.family.labels) (Free.scheme_derives _) p h
    (hN i) (by omega) (hD i) le_rfl ((hB B le_rfl).2 i) a v

include lead owed simple in
theorem original {d : ℕ} (j : Axis) (a : S.Field d) (v : (freeTable R.family.labels).Field d)
    (h : Tendsto (fun k => ((ruler F J Z radii).U k d).symm (((radii.r k ^ d : ℝ) : ℂ) • a)) atTop (𝓝 v)) :
    Tendsto (fun k => ((ruler F J Z radii).U k (d+1)).symm
      (((radii.r k ^ (d+1) : ℝ) : ℂ) • F.sector.derivatives.deriv d j a))
      atTop (𝓝 ((Free.scheme R.family.labels).deriv d j v)) := by
  have hD := (tendsto_pi_nhds.mp (transport F J Z lead owed simple radii d)) j
  have applied := Dash.arcing hD h
  apply applied.congr
  intro k
  apply ((ruler F J Z radii).U k (d+1)).injective
  change (ruler F J Z radii).U k (d+1) ((ruler F J Z radii).r k • ((ruler F J Z radii).carry k (leaves F.sector.derivatives.deriv d j) _)) = _
  rw [← Complex.coe_smul,map_smul,(ruler F J Z radii).carries_f,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change ((ruler F J Z radii).r k : ℂ) • (F.sector.derivatives.deriv d j) ((((ruler F J Z radii).r k ^ d : ℝ) : ℂ) • a) = _
  rw [(F.sector.derivatives.deriv d j).map_smul,smul_smul,pow_succ,Complex.ofReal_mul,mul_comm]
  rfl

end YM.Integration.WilsonOneFrameFieldDerivative
end
