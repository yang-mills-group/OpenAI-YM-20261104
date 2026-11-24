import YM.Integration.WilsonReportFundedGram

/-! Simultaneous independently calibrated mixed physical Gram matrix,
with one actual Wilson representative per row and per reflected column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportMixedMatrix
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- Fixed finite lists may be the entire chosen homogeneous basis. The
total absolute error is paid at once, for the genuine finite mixed form. -/
theorem on_run (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (F : Final R.family f S) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
    (g : ℝ→ℝ) (hg : Coupling G g) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex) ≤ f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
    ∀ (d q l n : ℕ) (X : Fin l→RG17.Free R.family d) (Y : Fin n→RG17.Free R.family d) {A : ℝ},1 ≤ A →
      ∀ ε : ℝ,0 < ε → ∀ᶠ r in RG17.home,let k := berth R ((q+1)+25) (L.level r)
      ∀ s : ℝ,r/A ≤ s → s ≤ A*r → ∃ (a : Fin l→R.family.label d) (b : Fin n→R.family.label d),
        (∀ i,master L d r (a i)=J s d (X i)) ∧ (∀ j,master L d r (b j)=J r d (adjoint R d (Y j))) ∧
        ∀ᶠ z : UVIndex in L.lens,k < z.1 ∧
        (∑ i,∑ j,|WilsonOrdinaryMixedGram.mixed F J d r s (X i) (Y j) -
          (value L d ![a i,b j] r k z.1 z.2).re|) ≤ ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,early⟩ :=
    WilsonReportEarlyFlags.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro d q l n X Y A hA ε hε
  let Γ : Census (Fin 2) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  have sep : {detectors} ⊆ conf 2 := singleton_subset_iff.mpr detectors_in
  obtain ⟨t,ht,shore,_⟩ := early Γ (fun _=>d) isCompact_singleton sep
  have located := shore detectors (mem_singleton _)
  have genuine := WilsonReportPrescribedFrame.present F J H paid
  obtain ⟨e,reps⟩ := (paying d).affordability
  obtain ⟨c,scaled⟩ := WilsonReportMixedScale.coordinates F J genuine (fun _ : Fin 1=>d) hA
  let fee := ε/(1+(l:ℝ)*n)
  have den : 0<1+(l:ℝ)*n := by positivity
  have pf : 0<fee := div_pos hε den
  have total : (l:ℝ)*n*fee ≤ ε := by
    have buy : fee*(1+(l:ℝ)*n)=ε := div_mul_cancel₀ ε den.ne'
    linarith only [buy,pf]
  have rows (i : Fin l) (j : Fin n) :=
    WilsonReportFundedGram.at_fields hG pace hB J genuine Q L pegs placed scene g hg ht located d q (e+1)
      (X i) (Y j) hA pf
  have heat := (Station.hat_rate R.family.path.levels hG).comp pegs.level.growing
  have first (i : Fin l) := heat.eventually_ge_atTop ((2*A)^c 0*‖X i‖)
  have second (j : Fin n) := heat.eventually_ge_atTop ‖adjoint R d (Y j)‖
  filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (rows i)),reps,scaled,
    eventually_all.mpr first,eventually_all.mpr second,hg.positive] with r rows bank scale first second gp
  dsimp only at bank rows ⊢
  intro s low high
  let k := berth R ((q+1)+25) (L.level r)
  let β := R.family.path.levels.clock.hatBeta (L.level r)
  have bp : 0<β := (R.family.path.levels.fits.delayed _).trans' zero_lt_one
  let v (i : Fin l) := (J r d).symm (J s d (X i))
  choose a costA fieldA using fun i=>bank.1 (v i)
  choose b costB fieldB using fun j=>bank.1 (adjoint R d (Y j))
  have fields (i) : master L d r (a i)=J s d (X i) :=
    (fieldA i).trans (LinearEquiv.apply_symm_apply _ _)
  refine ⟨a,b,fields,fieldB,?_⟩
  have aPrice (i) : mass R.family d (L.shift d r (a i)) ≤ β^(e+1) := by
    have h := scale.2 (fun _=>s) (fun _=>⟨low,high⟩) 0 (X i)
    rw [pow_succ]
    exact (costA i).trans (mul_le_mul_of_nonneg_left (h.trans (first i)) (pow_nonneg bp.le _))
  have bPrice (j) : mass R.family d (L.shift d r (b j)) ≤ β^(e+1) := by
    rw [pow_succ]
    exact (costB j).trans (mul_le_mul_of_nonneg_left (second j) (pow_nonneg bp.le _))
  have genuinePair (i : Fin l) (j : Fin n) : ∀ᶠ z : UVIndex in L.lens,
      k < z.1 ∧ |WilsonOrdinaryMixedGram.mixed F J d r s (X i) (Y j) -
        (value L d ![a i,b j] r k z.1 z.2).re| ≤ fee*(g r)^q := by
    apply rows i j s low high ![a i,b j] _ (fields i) (fieldB j)
    intro c
    fin_cases c
    · exact aPrice i
    · exact bPrice j
  filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (genuinePair i)),
    (large_mesh f (k+1)).filter_mono L.certified] with z entries late
  refine ⟨late,?_⟩
  calc
    _ ≤ ∑ _ : Fin l,∑ _ : Fin n,fee*(g r)^q :=
      sum_le_sum fun i _=>sum_le_sum fun j _=>(entries i j).2
    _ = ((l:ℝ)*n*fee)*(g r)^q := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right total (pow_nonneg gp.le _)

end YM.Integration.WilsonReportMixedMatrix
end

