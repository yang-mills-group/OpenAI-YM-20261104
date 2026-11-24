import YM.Integration.WilsonMatrixTicketLanesSmearedRows
import YM.Integration.WilsonOrdinaryMixedDetectors

/-! Fixed signed compact determining profiles in the ultraviolet running frame.
The test radius and all exterior registers are set before the central field or perturbative order is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesSmearedPivot
open Function Set Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedRows
open private cost clm_bound from YM.Integration.WilsonOrdinaryMixedDetectors
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {Y : (Bel R.family.book).Hierarchy} (lead : PhysMS.Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d) (simple : G.Simple) {d : ℕ}

structure Profiles (R : Run G) (d : ℕ) where
  probes : Contacts.Foci (Bel R.family.book) d
  level : ℕ
  fits : ∀ i : probes.index, RG05Readout.Bay.sand (probes.shell i).point (R.family.S.a level/16) ⊆ conf ((probes.shell i).n+1)

def test (B : Profiles R d) (i : B.probes.index) : Test ((B.probes.shell i).n+1) :=
  RG05Readout.Bay.Packet (C:=R.family) (B.probes.shell i).point B.level (B.fits i)

def row (B : Profiles R d) (r : ℝ) : S.Field d →ₗ[ℂ] (B.probes.index → ℂ) :=
  LinearMap.pi fun i => observation F J Z (B.probes.shell i) (test B i) r d

include lead paid simple in
/-- The probes, compact test shapes, and one fixed finite constant work simultaneously on every original field. -/
theorem submitted (d : ℕ) (D : Contacts.Foci (Bel R.family.book) d) :
    ∃ B : Profiles R d, B.probes = D ∧ ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail, ∀ y : S.Field d,
      ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖row F J Z B r y‖ := by
  let basis := Module.finBasis ℝ ((Bel R.family.book).Field d)
  let q := D.decoder.toContinuousLinearMap
  let C := ‖q‖+1
  let W := cost basis+1
  have pos : 0 < C := by dsimp [C]; positivity
  have qnn : 0 ≤ cost basis := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have Wpos : 0 < W := by dsimp [W]; positivity
  let δ := (4*C*W)⁻¹
  have tol : 0 < δ := by dsimp [δ]; positivity
  have fits : ∀ᶠ k : ℕ in atTop, ∀ i : D.index,
      RG05Readout.Bay.sand (D.shell i).point (R.family.S.a k/16) ⊆ conf ((D.shell i).n+1) := by
    refine eventually_all.mpr fun i => ?_
    have h := RG05Readout.Bay.converging (C:=R.family) (D.shell i).point (D.shell i).clear (fun _ => (D.shell i).point)
      tendsto_const_nhds (fun _ => (0:ℂ)) continuousOn_const 1 one_pos
    exact h.mono fun _ hk => hk.choose
  have treeScores : ∀ᶠ k : ℕ in atTop, ∀ i : D.index, ∀ j, ∃ fit :
      RG05Readout.Bay.sand (D.shell i).point (R.family.S.a k/16) ⊆ conf ((D.shell i).n+1),
      ‖(RG05Readout.Bay.Packet (C:=R.family) (D.shell i).point k fit).applyTo (freeKernel (R:=R) (D.shell i) (basis j)) -
        freeKernel (R:=R) (D.shell i) (basis j) (D.shell i).point‖ ≤ δ := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    exact RG05Readout.Bay.converging (C:=R.family) (D.shell i).point (D.shell i).clear (fun _ => (D.shell i).point)
      tendsto_const_nhds _ (((Bel R.family.book).smooth_read Y.smooth _).continuousOn) δ tol
  obtain ⟨k,fitting,treeEq⟩ := (fits.and treeScores).exists
  let B : Profiles R d := ⟨D,k,fitting⟩
  let V := WilsonMatrixTicketLanesNormalizedPivot.reference D
  let b (r : ℝ) := (row F J Z B r).comp (homogeneous F J Z r d).toLinearMap
  have normalized : ∀ᶠ r in trail, ∀ i : D.index, ∀ j, ‖b r (basis j) i - tree (R:=R) (D.shell i) (test B i) Y d (basis j)‖ < δ := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    have h := Metric.tendsto_nhds.mp (converges F J Z lead paid simple (D.shell i) (test B i) (basis j)) δ tol
    exact h.mono fun r hr => by rwa [dist_eq_norm] at hr
  refine ⟨B,rfl,2*C,by positivity,?_⟩
  filter_upwards [normalized] with r hr y
  let x := (homogeneous F J Z r d).symm y
  have each (j) : ‖(b r - V) (basis j)‖ ≤ 2*δ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have limit := (treeEq i j).choose_spec
    have origin : ‖tree (R:=R) (D.shell i) (test B i) Y d (basis j) - V (basis j) i‖ ≤ δ := by
      change ‖tree (R:=R) (D.shell i) (test B i) Y d (basis j) - (Bel R.family.book).spectra d (basis j) (D.shell i)‖ ≤ δ
      rw [on_tree, ← known (R:=R) (D.shell i) (basis j)]
      exact limit
    have triangle := dist_triangle (b r (basis j) i) (tree (R:=R) (D.shell i) (test B i) Y d (basis j)) (V (basis j) i)
    simp only [dist_eq_norm] at triangle
    exact (triangle.trans (add_le_add (hr i j).le origin)).trans_eq (two_mul δ).symm
  let H := (b r - V).toContinuousLinearMap.restrictScalars ℝ
  have bound : ‖H‖ ≤ cost basis*(2*δ) := clm_bound basis H (by positivity) each
  have gap : ‖b r x-V x‖ ≤ W*(2*δ)*‖x‖ := by
    apply (H.le_opNorm x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact bound.trans (mul_le_mul_of_nonneg_right (by dsimp [W]; linarith) (by positivity))
  have first : ‖x‖ ≤ C * ‖V x‖ := by
    calc
      ‖x‖ = ‖q (V x)‖ := congrArg norm (D.detects x).symm
      _ ≤ ‖q‖ * ‖V x‖ := q.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)
  have triangle : ‖V x‖ ≤ ‖b r x-V x‖ + ‖b r x‖ := by
    rw [norm_sub_rev]; simpa only [sub_add_cancel] using norm_add_le (V x-b r x) (b r x)
  have absorbed := first.trans (mul_le_mul_of_nonneg_left (triangle.trans (add_le_add gap le_rfl)) pos.le)
  have bill : C*(W*(2*δ)*‖x‖ + ‖b r x‖) = ‖x‖/2 + C*‖b r x‖ := by dsimp [δ]; field_simp [ne_of_gt pos,ne_of_gt Wpos]; ring
  rw [bill] at absorbed
  have result : ‖x‖ ≤ 2*C*‖b r x‖ := by linarith
  have seen : b r x = row F J Z B r y := by
    change row F J Z B r (homogeneous F J Z r d ((homogeneous F J Z r d).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
  rwa [seen] at result

include lead paid simple in
theorem original (d : ℕ) : ∃ B : Profiles R d, ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail, ∀ y : S.Field d,
    ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖row F J Z B r y‖ := by
  obtain ⟨D⟩ := Contacts.Foci.available Y.translations d
  obtain ⟨B,_,K,hK,he⟩ := submitted F J Z lead paid simple d D
  exact ⟨B,K,hK,he⟩

end YM.Integration.WilsonMatrixTicketLanesSmearedPivot
