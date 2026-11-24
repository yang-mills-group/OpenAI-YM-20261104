import YM.Integration.WilsonReportAnchoredReading
import YM.Integration.WilsonReportDetectorMesh
import YM.Pier.Blocks.Plate

/-! One signed numerical reflected two-point array on the original physical
report.  The continuum fields retain their independently calibrated radii,
with the actual second leg reflected. The error includes the finite-cell
displacement at the genuine detector as well as all the earlier flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportReflectedGram
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportEarlySmearing
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}

def adjoint (R : Run G) (d : ℕ) (w : RG17.Free R.family d) : RG17.Free R.family d :=
  (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) d timeAxis w

/-- Signed joint moment of the two actual reported fields on one coarse sample. -/
def value (L : Layout F) (d : ℕ) (w : Fin 2→R.family.label d) (r : ℝ) (k N p : ℕ) : ℂ :=
  ∫ U,∏ j,coarse L (fun _ : Fin 2=>d) w r (N:=N) (cells R k p r detectors) j U
    ∂(OPE.Therm.scene R.family.path N p k)

private theorem triangle {a b c e : ℂ} {h : ℝ} (ha : ‖b-a‖≤h) (hb : ‖c-b‖≤h) (hc : ‖c-e‖≤h) :
    |a.re-e.re|≤3*h := by
  rw [←Complex.sub_re]
  apply (Complex.abs_re_le_norm _).trans
  calc
    _ ≤ ‖a-b‖+‖b-c‖+‖c-e‖ := by
      have first := dist_triangle a b c
      have second := dist_triangle a c e
      simp only [dist_eq_norm] at first second
      linarith only [first,second]
    _ ≤ _ := by rw [norm_sub_rev a b,norm_sub_rev b c]; linarith only [ha,hb,hc]

theorem on_run (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (F : Final R.family f S) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
    (g : ℝ→ℝ) (hg : Coupling G g) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
    ∀ (d q : ℕ) (v w : RG17.Free R.family d) {A : ℝ},1≤A → ∀ ε : ℝ,0<ε → ∀ᶠ r in RG17.home,
      let k := berth R ((q+1)+25) (L.level r)
      ∀ s : ℝ,r/A ≤ s → s ≤ A*r → ∃ b : Fin 2→R.family.label d,
        (master L d r (b 0) = J s d v ∧ master L d r (b 1) = J r d (adjoint R d w)) ∧
        ∀ᶠ i : UVIndex in L.lens,k < i.1 ∧ |WilsonOrdinaryMixedGram.mixed F J d r s v w -
          (value L d b r k i.1 i.2).re| ≤ ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,early⟩ :=
    WilsonReportEarlyFlags.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro d q v w A hA ε hε
  let D : Fin 2→ℕ := fun _=>d
  let K : Set (Points 2) := {detectors}
  have sep : K ⊆ conf 2 := singleton_subset_iff.mpr detectors_in
  have P := WilsonReportPrescribedFrame.present F J H paid
  obtain ⟨M,δ,hM,hδ,lip⟩ := P.confines D K isCompact_singleton sep
  obtain ⟨e,ranges⟩ := WilsonReportMixedScale.coordinates F J P D hA
  let u₁ := adjoint R d w
  let c := (2*A)^e 0*‖v‖+‖u₁‖+1
  have a0 : 0<A := zero_lt_one.trans_le hA
  have c0 : 0<c := by dsimp only [c]; positivity
  have cap : ∀ᶠ r in RG17.home,c ≤ R.family.path.levels.clock.hatBeta (L.level r) :=
    ((Station.hat_rate R.family.path.levels hG).comp pegs.level.growing).eventually_ge_atTop c
  have he : 0<ε/3 := by positivity
  have money := WilsonReportDetectorMesh.small hG pace hB g hg q (mul_pos hM (mul_pos c0 c0)) he
  have width := WilsonReportDetectorMesh.small hG pace hB g hg q zero_lt_one hδ
  dsimp only at money width
  rw [←placed] at money width
  let Γ : Census (Fin 2) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  let all : Γ.Mode := ⟨univ,mem_univ _⟩
  obtain ⟨t,_,shore,flags⟩ := early Γ D isCompact_singleton sep
  have trueShore := shore detectors (mem_singleton _)
  have small := (Trace.Pilot.Coupling.conforms hG hg).eventually (gt_mem_nhds zero_lt_one)
  have refs := pegs.level.growing.eventually_ge_atTop (R.family.ref d)
  have reflect := WilsonReportDetectorMesh.reflected F J P d
  filter_upwards [flags (q+1) q 1 (ε/3) he,lip,ranges,cap,money,width,refs,reflect,hg.positive,small] with
    r field slope norms cap meshCost enters ref echo gp gs
  dsimp only at field ⊢
  obtain ⟨deep,envelope,mesh,buy⟩ := field
  let m := L.level r
  let k := berth R ((q+1)+25) m
  let β := R.family.path.levels.clock.hatBeta m
  have bp : 0<β := (R.family.path.levels.fits.delayed m).trans' zero_lt_one
  let z := address (R.family.S.a k/r) detectors
  let X := tag (R.family.S.a k/r) z
  have hr := norms.1
  have close : ‖X-detectors‖ ≤ 1/β^(q+1) := calc
    _ ≤ (4*(2:ℝ))*(R.family.S.a k/r) := by
      have geometric := Extraction.approximate (div_pos (R.family.S.a_pos k) hr) detectors
      rw [dist_eq_norm] at geometric
      apply geometric.trans_eq
      norm_num
    _ = ((4*(2:ℝ))*R.family.S.a k)/r := by ring
    _ ≤ (r/β^(q+1))/r := div_le_div_of_nonneg_right mesh.1 hr.le
    _ = _ := by field_simp
  have onSite : ‖X-detectors‖ ≤ δ :=
    close.trans (enters.trans (mul_le_of_le_one_right hδ.le (pow_le_one₀ gp.le gs.le)))
  have moves := slope detectors (mem_singleton _) X onSite
  have geo := WilsonReportAnchoredReading.rescale (R.family.S.a k) hr z
  have conf : tag (R.family.S.a k) z∈conf 2 := geo ▸ Work.A04.scale_conf r hr moves.1
  intro s low high
  let v₀ := (J r d).symm (J s d v)
  let pair : Fin 2→RG17.Free R.family d := ![v₀,u₁]
  have bound : ‖v₀‖ ≤ (2*A)^e 0*‖v‖ := norms.2 (fun _=>s) (fun _=>⟨low,high⟩) 0 v
  have bnd (j : Fin 2) : ‖pair j‖ ≤ c := by
    have p0 : 0≤(2*A)^e 0*‖v‖ := by positivity
    have p1 := norm_nonneg u₁
    fin_cases j
    · change ‖v₀‖ ≤ (2*A)^e 0*‖v‖+‖u₁‖+1
      linarith only [bound,p1]
    · change ‖u₁‖ ≤ (2*A)^e 0*‖v‖+‖u₁‖+1
      linarith only [p0]
  obtain ⟨b,labels,fee⟩ := buy pair (fun j=>by simpa only [pow_one] using (bnd j).trans cap)
  refine ⟨b,⟨?_,?_⟩,?_⟩
  · have eq : master L d r (b 0) = J r d ((J r d).symm (J s d v)) := labels 0
    exact eq.trans (LinearEquiv.apply_symm_apply _ _)
  · exact labels 1
  let η := (ε/3)*(g r)^q
  have hn : 0<η := mul_pos he (pow_pos gp _)
  have actual := WilsonReportAnchoredReading.original hG L r D b (fun _=>ref) k z conf η hn
  filter_upwards [actual,(large_mesh f (k+1)).filter_mono L.certified] with i act later
  have hk : k < i.1 := by omega
  refine ⟨hk,?_⟩
  let x := cells R k i.2 r detectors
  have placedSites := placement (p:=i.2) hr envelope trueShore
  have near : Neighbor R detectors r (r/(t:ℝ)/4) x := fun j=>(placedSites j).trans mesh.2
  obtain ⟨_,retained⟩ := fee detectors (mem_singleton _) i.2
  obtain ⟨live,invoice⟩ := retained i.1 hk x near all
  have raw := (identity L D b r hk.le x all live).2
  let actualValue (y : Points 2) := S.classMoment S D (r • y) (fun j=>J r d (pair j))
  let fineMoment := moment (n:=R.family.side i.1 i.2) (R.family.beta i.1 i.2)
    (fun U=>∏ j,fine L D b r (p:=i.2) hk.le x j U)
  let coarseMoment := value L d b r k i.1 i.2
  have e₁ : ‖actualValue X-actualValue detectors‖ ≤ η := by
    have prod : (∏ j,‖pair j‖) ≤ c*c := by
      rw [Fin.prod_univ_two]
      exact mul_le_mul (bnd 0) (bnd 1) (norm_nonneg _) c0.le
    calc
      _ ≤ M*(∏ j,‖pair j‖)*‖X-detectors‖ := moves.2 pair
      _ ≤ (M*(c*c))*(1/β^(q+1)) := mul_le_mul (mul_le_mul_of_nonneg_left prod hM.le) close
        (norm_nonneg _) (mul_nonneg hM.le (mul_nonneg c0.le c0.le))
      _ = (M*(c*c))/β^(q+1) := by ring
      _ ≤ _ := meshCost
  have e₂ : ‖fineMoment-actualValue X‖ ≤ η := by
    have estimate := (act hk.le).le
    rw [←geo] at estimate
    have lab : (fun j=>master L (D j) r (b j))=(fun j=>J r d (pair j)) := funext labels
    rw [lab] at estimate
    exact estimate
  have e₃ : ‖fineMoment-coarseMoment‖ ≤ η := by
    change ‖moment (R.family.beta i.1 i.2) (fineJob (fine L D b r hk.le x) all.val) -
      ∫ U,fineJob (coarse L D b r (N:=i.1) x) all.val U ∂OPE.Therm.scene R.family.path i.1 i.2 k‖ ≤ η
    rw [raw]
    exact invoice
  have measured : WilsonOrdinaryMixedGram.mixed F J d r s v w=(actualValue detectors).re := echo s v w
  rw [measured]
  apply (triangle e₁ e₂ e₃).trans
  dsimp only [η]
  linarith

end YM.Integration.WilsonReportReflectedGram
end

