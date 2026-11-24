import YM.Integration.WilsonReportEarlyConnected
import YM.Pier.Lair.Travel

/-! Numerical comparison for the actual mixed original position fields at any
independently chosen bounded ratios.  The fine and reported fields share the
one installed physical layout, and the old fixed tower is evaluated at the
specified radii before any period is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportMixedScale
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportMomentDifference
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- Uniformly compare the two actual prescribed physical coordinates on the same
continuum extraction, before choosing the finite independent radii. -/
theorem coordinates (F : Spec.Final R.family f S) (J : ℝ→PhysMS.tower S)
    (P : Pier.Lair.Present F J) {n : ℕ} (d : Fin n→ℕ) {A : ℝ} (hA : 1≤A) :
    ∃ e : Fin n→ℕ,∀ᶠ r in RG17.home,0<r ∧ ∀ s : Fin n→ℝ,(∀ j : Fin n,r/A ≤ s j ∧ s j ≤ A*r) →
      ∀ (j : Fin n) (v : RG17.Free R.family (d j)),
      ‖(J r (d j)).symm (J (s j) (d j) v)‖ ≤ (2*A)^e j*‖v‖ := by
  choose e τ hτ change using fun j : Fin n=>Pier.Lair.ranges F P (d j)
  refine ⟨e,?_⟩
  have a : 0 < A := zero_lt_one.trans_le hA
  have small (j : Fin n) : ∀ᶠ r in RG17.home,r < τ j/A :=
    (gt_mem_nhds (div_pos (hτ j) a)).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ r in RG17.home,0 < r := self_mem_nhdsWithin
  filter_upwards [eventually_all.mpr small,pos] with r small hr
  refine ⟨hr,?_⟩
  intro s hs j v
  have sj : 0 < s j := (div_pos hr a).trans_le (hs j).1
  have before : A*r ≤ τ j := by
    rw [mul_comm]
    exact (lt_div_iff₀ a).mp (small j) |>.le
  have rτ : r ≤ τ j := (le_mul_of_one_le_left hr.le hA).trans before
  by_cases h : s j ≤ r
  · have times : r ≤ s j*A := (div_le_iff₀ a).mp (hs j).1
    have ratio : 2*r/s j ≤ 2*A := (div_le_iff₀ sj).mpr (by linarith only [times])
    have bound := (change j (s j) r sj h rτ).right (J (s j) (d j) v)
    calc
      _ ≤ (2*r/s j)^e j*‖v‖ := by simpa using bound
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ratio _) (norm_nonneg _)
  · have ratio : 2*s j/r ≤ 2*A := (div_le_iff₀ hr).mpr (by linarith only [(hs j).2])
    have bound := (change j r (s j) hr (le_of_lt (lt_of_not_ge h)) ((hs j).2.trans before)).left (J (s j) (d j) v)
    calc
      _ ≤ (2*s j/r)^e j*‖v‖ := by simpa using bound
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ratio _) (norm_nonneg _)

/-- One original finite torus and one reporter for all independently prescribed scale labels. -/
theorem on_run (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
    (g : ℝ→ℝ) (hg : Trace.Pilot.Coupling G g) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
    ∀ {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) {K : Set (Points n)},
      IsCompact K → K⊆conf _ → ∃ t : ℕ,1≤t ∧ (∀ X∈K, AtShore t X) ∧
    ∀ (o q power : ℕ) {A : ℝ},1≤A → ∀ ε : ℝ,0<ε → ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ EnvelopeRange R m k t o r ∧
      ((4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧ (4*n:ℝ)*C.S.a k ≤ r/(t:ℝ)/4) ∧
      ∀ rad : Fin n→ℝ,(∀ j : Fin n,r/A ≤ rad j ∧ rad j ≤ A*r) →
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J (rad j) (d j) (v j)) ∧
      ∀ X∈K,∀ p : ℕ, (∃ x : Fin n→Site (C.side k p),Neighbor R X r ((4*n:ℝ)*C.S.a k) x) ∧
      ∀ N : ℕ,∀ cut : k < N,∀ x : Fin n→Site (C.side k p),Neighbor R X r (r/(t:ℝ)/4) x →
      ∀ s : Γ.Mode,
      ‖(connected (microscopic Γ C (fine L d w r cut.le x))).part s -
        (connected (reported Γ C (N:=N) (coarse L d w r (N:=N) x))).part s‖ ≤ ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,early⟩ :=
    WilsonReportEarlyConnected.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro n Γ d K compact inside
  obtain ⟨t,ht,shore,valid⟩ := early Γ d compact inside
  refine ⟨t,ht,shore,?_⟩
  intro o q power A hA ε hε
  obtain ⟨e,ranges⟩ := coordinates F J (WilsonReportPrescribedFrame.present F J H paid) d hA
  have covers (j : Fin n) : ∀ᶠ r in RG17.home,(2*A)^e j≤R.family.path.levels.clock.hatBeta (L.level r) :=
    ((Next.Rank.Station.hat_rate R.family.path.levels hG).comp pegs.level.growing).eventually_ge_atTop _
  filter_upwards [valid o q (power+1) ε hε,ranges,eventually_all.mpr covers] with r good bounds covers
  dsimp only at good ⊢
  obtain ⟨deep,fit,mesh,ready⟩ := good
  refine ⟨deep,fit,mesh,?_⟩
  intro rad hrs v hv
  let base (j : Fin n) := (J r (d j)).symm (J (rad j) (d j) (v j))
  let β := R.family.path.levels.clock.hatBeta (L.level r)
  have b0 : 0≤β := zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have cost (j : Fin n) : ‖base j‖≤β^(power+1) := calc
    ‖base j‖ ≤ (2*A)^e j*‖v j‖ := bounds.2 rad hrs j (v j)
    _ ≤ β*β^power := mul_le_mul (covers j) (hv j) (norm_nonneg _) b0
    _ = β^(power+1) := by rw [pow_succ,mul_comm]
  obtain ⟨w,field,report⟩ := ready base cost
  refine ⟨w,?_,report⟩
  intro j
  simpa only [base,LinearEquiv.apply_symm_apply] using field j

end YM.Integration.WilsonReportMixedScale
end

