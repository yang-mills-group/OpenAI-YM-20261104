import YM.Integration.WilsonReportEarlyConnected

/-! Actual spatial testing of the complete early connected remainder.
Cells are the original torus wrap of the canonical ceiling address on the
true finer grid, and the position profile may be signed or complex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportEarlySmearing
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open Extra.Trajectories (connected)
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportMomentDifference
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

/-- The original discrete address evaluated in the fixed physical r chart. -/
def cells (R : Run G) {n : ℕ} (k p : ℕ) (r : ℝ) (X : Points n) : Fin n→Site (R.family.side k p) :=
  wrap (R.family.side k p) ∘ address (R.family.S.a k/r) X

theorem placement {n m k t o p : ℕ} {r : ℝ} (hr : 0<r) (E : EnvelopeRange R m k t o r)
    {X : Points n} (shore : AtShore t X) : Neighbor R X r ((4*n:ℝ)*R.family.S.a k) (cells R k p r X) := by
  let T := R.family.S
  let P := r • X
  have radius : (1/2:ℝ) ≤ T.radius p := div_le_div_of_nonneg_right (mod_cast (T.period p).property) (by norm_num)
  have rt : r*(t:ℝ)<T.radius p := by
    nlinarith only [radius,E.radius,mul_nonneg hr.le (Nat.cast_nonneg (α:=ℝ) t)]
  have inside : P∈Fund T p n := by
    intro i a
    have v : |P i a|≤‖P i‖ := PiLp.norm_apply_le (P i) a
    have p1 : ‖P i‖≤r*(t:ℝ) := by
      change ‖r • X i‖≤_
      rw [norm_smul,Real.norm_of_nonneg hr.le]
      exact mul_le_mul_of_nonneg_left (shore.1 i) hr.le
    have u := abs_lt.mp (v.trans_lt (p1.trans_lt rt))
    exact ⟨u.1,u.2.le⟩
  obtain ⟨x,ax,_⟩ := Extraction.corners (N:=k) inside
  have ac : address (T.a k) P=fun i=>lift (x i) := ax
  have rescale : address (T.a k/r) X=address (T.a k) P := by
    funext i a
    change ⌈X i a/(T.a k/r)⌉=⌈(r*X i a)/(T.a k)⌉
    congr 1
    field_simp
  have same : cells R k p r X=x := by
    funext i
    change wrap (T.side k p) ((address (T.a k/r) X) i)=x i
    rw [rescale,ac,wrap_lift]
  rw [same]
  have exactGrid := Extraction.approximate (T.a_pos k) P
  rw [ac,dist_eq_norm] at exactGrid
  exact fun i=>(PiLp.norm_apply_le (tag (T.a k) (fun j=>lift (x j))-P) i).trans exactGrid

/-- The actual connected fine minus coarse value at the indicated wrapped
cell, with the fine labels and its coarse counterparts on their true laws. -/
def cellGap (L : Layout F) {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) (w : (j:Fin n)→R.family.label (d j))
    (r : ℝ) {k N : ℕ} (p : ℕ) (cut : k≤N) (s : Γ.Mode) (X : Points n) : ℂ :=
  let x := cells R k p r X
  (connected (microscopic Γ R.family (fine L d w r cut x))).part s-
    (connected (reported Γ R.family (N:=N) (coarse L d w r (N:=N) x))).part s

/-- Test the genuine finite spatial distribution, simultaneously at all
periods and fine cutoffs. The fixed test seminorm is exactly its integral
norm on K, independent of the perturbative order. -/
theorem tested (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
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
    ∀ {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) {K : Set (Points n)},IsCompact K → K⊆conf _ →
    ∀ (o q power : ℕ) (ε : ℝ),0<ε → ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ (4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J r (d j) (v j)) ∧
      ∀ p N : ℕ,∀ cut : k < N,∀ s : Γ.Mode,∀ ψ : Points n→ℂ,Continuous ψ →
      let Δ := cellGap L Γ d w r p cut.le s
      IntegrableOn (fun X=>ψ X*Δ X) K ∧
        ‖∫ X in K, ψ X*Δ X‖ ≤ (ε*(g r)^q)*(∫ X in K,‖ψ X‖) := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,claim⟩ :=
    WilsonReportEarlyConnected.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro n Γ d K compact inside o q power ε hε
  obtain ⟨t,_,stays,receive⟩ := claim Γ d compact inside
  filter_upwards [RG17.positiveLength,receive o q power ε hε] with r hr won
  dsimp only
  let m := L.level r
  let k := berth R (o+25) m
  obtain ⟨deep,E,mesh,receive⟩ := won
  refine ⟨deep,mesh.1,?_⟩
  intro v hv
  obtain ⟨w,values,report⟩ := receive v hv
  refine ⟨w,values,?_⟩
  intro p N cut s ψ hψ
  let Δ := cellGap L Γ d w r p cut.le s
  let b := ε*(g r)^q
  let τ := R.family.S.a k/r
  let V (z : Fin n → Cover) := (connected (microscopic Γ R.family
      (fine L d w r cut.le (wrap (R.family.side k p) ∘ z)))).part s-
    (connected (reported Γ R.family (N:=N)
      (coarse L d w r (N:=N) (wrap (R.family.side k p) ∘ z)))).part s
  have cellsM : Measurable (address (n:=n) τ) := measurable_to_countable'
    (fun z=>Extraction.measurable_segment (div_pos (R.family.S.a_pos _) hr) z)
  have measurable : Measurable Δ := (measurable_of_countable V).comp cellsM
  have point (X) (hX : X∈K) : ‖Δ X‖≤b := by
    have near := placement (p:=p) hr E (stays X hX)
    exact (report X hX p).2 N cut _ (fun j=> (near j).trans mesh.2) s
  have test : Integrable ψ (volume.restrict K) := hψ.continuousOn.integrableOn_compact compact
  have major : ∀ᵐ X ∂volume.restrict K,‖ψ X*Δ X‖≤‖ψ X‖*b := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with X hX
    exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (point X hX) (norm_nonneg _))
  have lim := test.norm.mul_const b
  refine ⟨lim.mono' (test.aestronglyMeasurable.mul measurable.aestronglyMeasurable) major,?_⟩
  exact (norm_integral_le_of_norm_le lim major).trans_eq ((integral_mul_const b _).trans (mul_comm ..))

end YM.Integration.WilsonReportEarlySmearing
end

