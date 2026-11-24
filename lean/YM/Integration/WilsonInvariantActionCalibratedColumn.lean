import YM.Integration.WilsonMatrixTicketLanesSmearedPair
import YM.Integration.WilsonInvariantActionCompensatedPair
import YM.Integration.WilsonInvariantActionIntegratedPair

/-! One signed row of the committed finite mixed matrix has nonzero action
response. The very same fixed test prices the physical Ward ratio and the
integrated two-leg posterior, before the clock is sent to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCalibratedColumn
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register Extraction Extraction.Order
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
    {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple : G.Simple)

include lead paid simple in
private theorem detected (B : Profiles R 4) (K : ℝ)
    (decode : ∀ᶠr in trail,∀ y:S.Field 4,‖(homogeneous F J Z r 4).symm y‖≤K*‖row F J Z B r y‖) :
    ∃j:B.probes.index,tree (B.probes.shell j) (test B j) H 4 (stepField R.family)≠0 := by
  let v:=stepField R.family
  let T:=fun j:B.probes.index=>tree (B.probes.shell j) (test B j) H 4 v
  have limit : Tendsto (fun r=>row F J Z B r (homogeneous F J Z r 4 v)) trail (𝓝 T) :=
    tendsto_pi_nhds.mpr fun j=>converges F J Z lead paid simple (B.probes.shell j) (test B j) v
  have lower : ‖v‖≤K*‖T‖ := le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_const_nhds.mul limit.norm) (decode.mono fun r hr=>by
      simpa only [LinearEquiv.symm_apply_apply] using hr (homogeneous F J Z r 4 v))
  by_contra! zero
  have none : T=0:=funext zero
  rw [none,norm_zero,mul_zero] at lower
  exact scale_alive simple H (norm_eq_zero.mp (le_antisymm lower (norm_nonneg v)))

def packet {e : Exterior (standard R.family.labels)} (w : (standard R.family.labels).Ref 4)
    (same : e=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w) (φ : Test (e.n+1)) : Test 2 :=
  cast (congrArg (fun E:Exterior (standard R.family.labels)=>Test (E.n+1)) same) φ

private theorem response {e : Exterior (standard R.family.labels)} (w : (standard R.family.labels).Ref 4)
    (same : e=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w) (φ : Test (e.n+1)) :
    tree (R:=R) e φ H 4 (stepField R.family)=(packet w same φ).applyTo (reading R.family w) := by
  subst e
  rw [on_tree]
  rfl

include lead paid simple in
theorem submitted (B : Profiles R 4)
    (sites : ∀j:B.probes.index,∃w:(standard R.family.labels).Ref 4,
      B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w)
    (K : ℝ) (decode : ∀ᶠr in trail,∀ y:S.Field 4,‖(homogeneous F J Z r 4).symm y‖≤K*‖row F J Z B r y‖)
    {P : ℝ→Spin.change S 4} {δ g : ℝ→ℝ} (same : ∀ᶠr in trail,J r 4=P r)
    (cent : ∀ᶠr in trail,AlignV F.room.kernel F.sector H (P r)) (cal : TendC F P δ) (coupling : Coupling G g) :
    ∃(j:B.probes.index) (w:(standard R.family.labels).Ref 4)
      (hs:B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w),
      let φ:=packet w hs (test B j)
      let c:=tree (B.probes.shell j) (test B j) H 4 (stepField R.family)
      let b:=fun r=>homogeneous F J Z r 4 ((Bel R.family.book).project 4 w)
      let y:=fun r=>J r 4 (stepField R.family)
      let cov:=fun r=>WilsonInvariantActionPairCovariance.tested (y r) (b r) r φ
      c≠0 ∧ Tendsto cov trail (𝓝 c) ∧
      (∀ (cut : (N p:ℕ)→Fin (N+1)) (r:ℝ) (hr:0<r),
        f.limits (fun p=>suitable R.family.S p (Next.UVStress.dilate hr φ))
          (WilsonInvariantActionIntegratedPair.profile R cut (S.representative 4 (y r))
            (S.representative 4 (b r)) (Next.UVStress.dilate hr φ)) (cov r)) ∧
      ∀ᶠr in trail,WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ≠0 ∧
        ((r^4/(4*δ r):ℝ):ℂ)=cov r / WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ := by
  obtain ⟨j,hj⟩:=detected F J Z lead paid simple B K decode
  obtain ⟨w,hs⟩:=sites j
  refine ⟨j,w,hs,?_⟩
  intro φ c b y cov
  have central : ∀ᶠr in trail,AlignV F.room.kernel F.sector H (J r 4) :=
    (same.and cent).mono fun _ h=>h.1.symm ▸ h.2
  have lim : Tendsto cov trail (𝓝 c) := by
    change Tendsto _ _ (𝓝 (tree (B.probes.shell j) (test B j) H 4 (stepField R.family)))
    rw [response w hs]
    exact WilsonInvariantActionCompensatedPair.original F J Z lead paid simple w central φ
  refine ⟨hj,lim,fun cut r hr=>WilsonInvariantActionIntegratedPair.ordered F cut φ hr (y r) (b r),?_⟩
  filter_upwards [lim.eventually_ne hj,WilsonInvariantActionPairCovariance.charged F J simple same cal coupling] with r nz q
  have fee:=q (b r) φ
  have denom : WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ≠0 := by
    intro gone
    rw [gone,mul_zero] at fee
    exact nz fee
  exact ⟨denom,(eq_div_iff denom).mpr fee.symm⟩

end YM.Integration.WilsonInvariantActionCalibratedColumn
