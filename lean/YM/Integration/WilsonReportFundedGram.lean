import YM.Integration.WilsonReportReflectedGram

/-! The actual mixed two-scale projection at already selected grade labels,
with the identical regulated fine data in every subsequent matrix entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFundedGram
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportEarlySmearing WilsonReportReflectedGram
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}

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

/-- The original mixed detector can be tested with any literal pair of pre-funded
fine labels representing its two continuum fields. The same such label may
therefore be used throughout a full row or column of the finite matrix. -/
theorem at_fields (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
    (J : ℝ→PhysMS.tower S) (P : Pier.Lair.Present F J) {u : Filter UVIndex}
    (Q : Lenses.Mantle F u) (L : Layout F) (pegs : Pegs Q L)
    (placed : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (scene : Pier.Scene.ScenePlan R F L) (g : ℝ→ℝ) (hg : Coupling G g)
    {t : ℕ} (ht : 1 ≤ t) (trueShore : AtShore t detectors) (d q power : ℕ) (v w : RG17.Free R.family d)
    {A : ℝ} (hA : 1 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in RG17.home,let k := berth R ((q+1)+25) (L.level r)
      ∀ s : ℝ,r/A ≤ s → s ≤ A*r → ∀ b : Fin 2→R.family.label d,
        (∀ j,mass R.family d (L.shift d r (b j)) ≤ R.family.path.levels.clock.hatBeta (L.level r)^power) →
        master L d r (b 0) = J s d v → master L d r (b 1) = J r d (adjoint R d w) →
        ∀ᶠ i : UVIndex in L.lens,k < i.1 ∧ |WilsonOrdinaryMixedGram.mixed F J d r s v w -
          (value L d b r k i.1 i.2).re| ≤ ε*(g r)^q := by
  let D : Fin 2→ℕ := fun _=>d
  let K : Set (Points 2) := {detectors}
  have sep : K ⊆ conf 2 := singleton_subset_iff.mpr detectors_in
  obtain ⟨M,δ,hM,hδ,lip⟩ := P.confines D K isCompact_singleton sep
  obtain ⟨e,ranges⟩ := WilsonReportMixedScale.coordinates F J P D hA
  let u₁ := adjoint R d w
  let c := (2*A)^e 0*‖v‖+‖u₁‖+1
  have a0 : 0<A := zero_lt_one.trans_le hA
  have c0 : 0<c := by dsimp only [c]; positivity
  have he : 0<ε/3 := by positivity
  have money := WilsonReportDetectorMesh.small hG pace hB g hg q (mul_pos hM (mul_pos c0 c0)) he
  have width := WilsonReportDetectorMesh.small hG pace hB g hg q zero_lt_one hδ
  dsimp only at money width
  rw [←placed] at money width
  let Γ : Census (Fin 2) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  let all : Γ.Mode := ⟨univ,mem_univ _⟩
  have flags := scene.allFlags Γ D (q+1) t (q+1) power ht
  have cash := WilsonReportConnectedCurrency.absorb R hG pace hB g hg 0 q zero_lt_one he
  dsimp only at cash
  rw [←placed] at cash
  have small := (Trace.Pilot.Coupling.conforms hG hg).eventually (gt_mem_nhds zero_lt_one)
  have refs := pegs.level.growing.eventually_ge_atTop (R.family.ref d)
  have reflect := WilsonReportDetectorMesh.reflected F J P d
  filter_upwards [flags,lip,ranges,money,width,refs,reflect,hg.positive,small,cash] with
    r field slope norms meshCost enters ref echo gp gs cash
  dsimp only
  obtain ⟨deep,_,envelope,mesh,buy⟩ := field
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
  intro s low high b budget left right
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
  have labels (j : Fin 2) : master L (D j) r (b j)=J r d (pair j) := by
    fin_cases j
    · change master L d r (b 0)=J r d v₀
      exact left.trans (LinearEquiv.apply_symm_apply _ _).symm
    · exact right
  let η := (ε/3)*(g r)^q
  have hn : 0<η := mul_pos he (pow_pos gp _)
  have actual := WilsonReportAnchoredReading.original hG L r D b (fun _=>ref) k z conf η hn
  filter_upwards [actual,(large_mesh f (k+1)).filter_mono L.certified] with i act later
  have hk : k < i.1 := by omega
  refine ⟨hk,?_⟩
  let x := cells R k i.2 r detectors
  have placedSites := placement (p:=i.2) hr envelope trueShore
  have near : Neighbor R detectors r (r/(t:ℝ)/4) x := fun j=>(placedSites j).trans mesh.2
  obtain ⟨_,retained⟩ := buy detectors trueShore i.2
  obtain ⟨live,base⟩ := retained i.1 hk b budget x near all
  have price := (cash i.1 i.2 (deep.trans hk).le).2
  have total := base.trans (by simpa only [Nat.add_zero,pow_zero,one_mul,mul_one] using price : _ ≤ η)
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
    exact total
  have measured : WilsonOrdinaryMixedGram.mixed F J d r s v w=(actualValue detectors).re := echo s v w
  rw [measured]
  apply (triangle e₁ e₂ e₃).trans
  dsimp only [η]
  linarith

end YM.Integration.WilsonReportFundedGram
end

