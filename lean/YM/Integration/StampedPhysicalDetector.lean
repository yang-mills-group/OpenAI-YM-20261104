import YM.Integration.ActualFoundryFiniteDetector
import YM.Frontier6.Multi.Toll.Stamps
import YM.Next.UV_STRESS.Layout
import YM.OPE.Log.PricePlot
import YM.OPE.ElementaryLog

/-! The native separated grid-product estimate has an actual regulator-dependent
matching label. Reading a specified physical candidate uses the difference
between the two labels at the original engineering cost. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.StampedPhysicalDetector
open Function Filter Lattice Wilson RG Cells StressFlux.Matching
open Frontier6.Road OPE.Orbits ActualFoundryDetectorSource
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

private lemma ceil_origin (N p : ℕ) : ceilSite C N p (0 : E4) = 0 := by
  change Lattice.wrap _ (fun _ => ⌈(0 : ℝ) / C.S.a N⌉) = 0
  simp only [zero_div, Int.ceil_zero]
  exact (Lattice.wrap _).map_zero

private lemma ceil_grid {N p j : ℕ} (h : j ≤ N) (x : Cover) :
    ceilSite C N p (C.S.gridPoint j x) = location C.S j N p x := by
  simpa only [zero_add, ceil_origin] using
    (WilsonExteriorGeometry.ceilSite_add_grid (C := C) (p := p) h (0 : E4) x)

variable {I : Type} [Fintype I] {d : I → ℕ} {D j N p : ℕ}

/-- Sampling true hierarchy-grid positions in a physical detector gives
exactly the native central compensated multipoint observable. -/
theorem central_grid (J : ℝ → PhysMS.tower S) (r : ℝ)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) (x : I → Cover)
    (z : S.Field D) (hj : j ≤ N) :
    detectorCentral J v r (fun i => C.S.gridPoint j (x i)) z N p =
      leafGap C j D d x (fun i => S.representative _ (PhysMS.Frame.born J r v i))
        N p (S.representative D z) := by
  apply congrArg₂ HSub.hSub
  · funext U
    simp only [WilsonWholeLimit.product, leaves, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i _
    change C.O N p _ (ceilSite C N p (C.S.gridPoint j (x i))) U = _
    rw [ceil_grid hj]
    rfl
  · funext U
    simp only [WilsonWholeLimit.product, Fintype.prod_unique]
    change C.O N p (S.representative D z) (ceilSite C N p 0) U = _
    rw [ceil_origin]

/-- A single original cell-price bank controls arbitrary label differences
linearly, simultaneously over all choices of the difference and its center. -/
theorem label_bound (F : Spec.Final C f S) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b₀ : ℕ, C.ref D ≤ b₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ b, b₀ ≤ b → ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ × ℕ in f.fuse,
        ∃ hb : b ≤ k.1, ∀ (v : C.label D) (x : Site (C.side k.1 k.2)),
          Interior ((center C.S k.2 hb x).chamber 0) (C.O k.1 k.2 v x) ∧
          (center C.S k.2 hb x).rootTest (C.beta k.1 k.2) (C.O k.1 k.2 v x) ≤
            ‖v‖ * (B * C.S.a b ^ (-(D : ℝ) - δ) + η) := by
  obtain ⟨b₀, hb₀, B, hB, H⟩ := F.room.copies.centered D δ 1 hδ one_pos
  refine ⟨b₀, hb₀, B, hB, fun b hb η hη => ?_⟩
  have hr : ∀ᶠ k : ℕ × ℕ in f.fuse, ∃ hb' : b ≤ k.1,
      ∀ (v : C.label D), ‖v‖ ≤ 1 → ∀ x : Site (C.side k.1 k.2),
        Interior ((center C.S k.2 hb' x).chamber 0) (C.O k.1 k.2 v x) ∧
          (center C.S k.2 hb' x).rootTest (C.beta k.1 k.2) (C.O k.1 k.2 v x) ≤
            B * C.S.a b ^ (-(D : ℝ) - δ) + η :=
    (Extraction.Order.fused f _).mpr (H b hb η hη)
  filter_upwards [hr] with k hk
  obtain ⟨hl, h⟩ := hk
  refine ⟨hl, fun v x => ?_⟩
  let u := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ ≤ 1 := by
    by_cases hv : v = 0
    · simp [u, hv]
    · simp [u, norm_smul, norm_ne_zero_iff.mpr hv]
  have huv : (‖v‖ : ℂ) • u = v := by
    by_cases hv : v = 0
    · simp [u, hv]
    · exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)) _
  have hlin : C.O k.1 k.2 v x = (‖v‖ : ℂ) • C.O k.1 k.2 u x := by
    rw [← (C.linearO k.1 k.2 D x).map_smul, huv]
  obtain ⟨hi, ht⟩ := h u hu x
  rw [hlin]
  refine ⟨hi.scale _, ?_⟩
  rw [Next.UVStress.root_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

/-- The native multipoint capture supplies a single actual matching label on
the ordered regulator tail. The same label and tail work for every physical
candidate, at the explicit engineering cost of the difference. -/
theorem stamped_candidates (F : Spec.Final C f S) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b₀ : ℕ, C.ref D ≤ b₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (J : ℝ → PhysMS.tower S) (r : ℝ)
        (v : (i : I) → (Climb.Bel C.book).Field (d i)) (x : I → Cover),
      ∀ b, b₀ ≤ b → ∀ (m j : ℕ) (cap price : ℝ),
        Stamped C m j b d x (fun i => S.representative _ (PhysMS.Frame.born J r v i))
          f D cap price → ∀ η : ℝ, 0 < η →
        ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ k : ℕ × ℕ in f.fuse, ∃ hb : b ≤ k.1,
          m ≤ k.1 ∧ Next.UVStress.quota C D m k.1 k.2 (Z k) ≤ cap ∧
          ∀ z : S.Field D,
            let T := center C.S k.2 hb 0
            let A := detectorCentral J v r (fun i => C.S.gridPoint j (x i)) z k.1 k.2
            Interior (T.chamber 0) A ∧
              T.rootTest (C.beta k.1 k.2) A ≤ price +
                ‖Z k - S.representative D z‖ * (B * C.S.a b ^ (-(D : ℝ) - δ) + η) := by
  obtain ⟨b₀, href, B, hB, hlabel⟩ := label_bound F D δ hδ
  refine ⟨b₀, href, B, hB, fun J r v x b hb m j cap price hs η hη => ?_⟩
  obtain ⟨Z, hz⟩ := hs.probe
  refine ⟨Z, ?_⟩
  have hmesh : ∀ᶠ k : ℕ × ℕ in f.fuse, j ≤ k.1 := by
    rw [Extraction.Order.fused, Extraction.Order.late]
    exact .of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop j
  filter_upwards [hz, hlabel b hb η hη, hmesh] with k hk hl hj
  obtain ⟨hlive, hm, hcap, hi, hroot⟩ := hk
  obtain ⟨_, hchange⟩ := hl
  refine ⟨hlive, hm, hcap, fun z => ?_⟩
  let raw := fun i => S.representative _ (PhysMS.Frame.born J r v i)
  let c := S.representative D z
  let A := leafGap C j D d x raw k.1 k.2 (Z k)
  let E := C.O k.1 k.2 (Z k - c) 0
  have hA : leafGap C j D d x raw k.1 k.2 c = A + E := by
    unfold A E leafGap
    rw [show C.O k.1 k.2 (Z k - c) 0 =
        C.O k.1 k.2 (Z k) 0 - C.O k.1 k.2 c 0 from
      ((C.linearO k.1 k.2 D 0).mk' _).map_sub _ _]
    abel
  have hphysical : detectorCentral J v r (fun i => C.S.gridPoint j (x i)) z k.1 k.2 =
      A + E := (central_grid J r v x z hj).trans hA
  dsimp only
  rw [hphysical]
  obtain ⟨hei, heroot⟩ := hchange (Z k - c) 0
  refine ⟨hi.plus hei, ?_⟩
  exact ((Cells.seamless F.room.cutoff k.1 k.2).semi (center C.S k.2 hlive 0)
    A E hi hei).trans (add_le_add hroot heroot)

open OPE OPE.Log MergeProof MergeProof.Ribbons


private def gridInvoice (D b m j : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (cap price : ℝ) (w : ℕ × ℕ) : Prop :=
  ∀ (hj : j < w.1) (hb : b ≤ w.1),
    let y := (wrap (C.side j w.2)) ∘ x
    let T := center C.S w.2 hb 0
    let q (i : I) := C.O w.1 w.2 (v i) ((C.S.toDepth hj.le w.2).embed (y i))
    (∀ i, loops C j w.2 (y i) (m + 1) = 0) →
    Next.Rank.Edition.Spaced (C.path.levels.budget j).B y →
    (∀ i, Interior (T.chamber 0) (q i)) →
    (∀ z : C.label D, Interior (T.chamber 0) (C.O w.1 w.2 z 0)) →
    ∃ z : C.label D, let gap := (fun U => ∏ i, q i U) - C.O w.1 w.2 z 0
      Next.UVStress.quota C D m w.1 w.2 z ≤ cap ∧ Interior (T.chamber 0) gap ∧
        T.rootTest (C.beta w.1 w.2) gap ≤ price

private theorem grid_capture (hC : C.Makes) {b m j D : ℕ}
    (x : I → Cover) (v : (i : I) → C.label (d i)) {cap price : ℝ}
    (shape : Plot C b m j x)
    (receipt : ∀ᶠ w in f.fuse, gridInvoice D b m j x v cap price w) :
    Stamped C m j b d x v f D cap price := by
  have hN := Cards.largeMesh f
  have hp : Tendsto (@Prod.snd ℕ ℕ) f.fuse atTop := tendsto_atTop.mpr fun t => by
    rw [Extraction.Order.fused, Extraction.Order.late]
    filter_upwards [f.per.cofinal.eventually_ge_atTop t] with p ht
    exact Eventually.of_forall fun _ => ht
  let fits (w : ℕ × ℕ) (z : C.label D) := ∃ hb : b ≤ w.1,
    m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 z ≤ cap ∧
    Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d x v w.1 w.2 z) ∧
    (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2) (leafGap C j D d x v w.1 w.2 z) ≤ price
  have available : ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ z, fits w z := by
    filter_upwards [hp.eventually shape.marsh, hN.eventually (near_center C b D hC),
      eventually_all.mpr (fun i => hN.eventually (near_center C b (d i) hC)),
      hN.eventually_gt_atTop j, receipt]
      with w scene counterFit fieldFit hj hinvoice
    have hj' : j < w.1 := hj
    let hb : b ≤ w.1 := shape.first.trans (m.le_succ.trans (shape.last.trans hj'.le))
    let T := center C.S w.2 hb 0
    let y := (wrap (C.side j w.2)) ∘ x
    let field (i : I) := C.O w.1 w.2 (v i) ((C.S.toDepth hj'.le w.2).embed (y i))
    have hi (i : I) : Interior (T.chamber 0) (field i) := by
      apply fieldFit i hb w.2
      rw [C.S.embeds_place, (scene.2 i).2]
      exact (shape.fit i).le.trans (C.S.strictAnti.antitone (shape.first.trans m.le_succ))
    have hc (z : C.label D) : Interior (T.chamber 0) (C.O w.1 w.2 z 0) :=
      counterFit hb w.2 _ (by rw [latzero]; simp [(C.S.a_pos b).le]) _
    obtain ⟨z, hcost, hlocal, hbound⟩ := hinvoice hj' hb
      (fun i => (scene.2 i).1) scene.1 hi hc
    have eq : leafGap C j D d x v w.1 w.2 z = (fun U => ∏ i, field i U) - C.O w.1 w.2 z 0 := by
      unfold leafGap leaves
      apply congrArg (fun a => a - C.O w.1 w.2 z 0)
      funext U
      simp only [field, y, comp_apply, Finset.prod_apply, Cells.location, dif_pos hj'.le]
    exact ⟨z, hb, m.le_succ.trans (shape.last.trans hj'.le), hcost,
      eq ▸ hlocal, eq ▸ hbound⟩
  let Z (w : ℕ × ℕ) : C.label D := if h : ∃ z, fits w z then h.choose else 0
  refine ⟨Z, available.mono ?_⟩
  intro w hw
  change fits w (Z w)
  simpa only [Z, dif_pos hw] using hw.choose_spec

/-- The cutoff-dependent input ceilings of the native fixed-load price are
sufficient on the original ordered tail. -/
theorem capture_on_grid (hC : C.Makes) {b m j D : ℕ}
    (x : I → Cover) (v : (i : I) → C.label (d i))
    {cap price : ℝ} {Q : I → ℝ} (paid : ShortPrice C cap price Q D d b m j)
    (shape : Plot C b m j x)
    (hQ : ∀ i, ∀ᶠ w : ℕ × ℕ in f.fuse, Next.UVStress.quota C (d i) j w.1 w.2
      (v i) ≤ Q i) : Stamped C m j b d x v f D cap price := by
  apply grid_capture hC x v shape
  filter_upwards [eventually_all.mpr hQ] with w hw
  intro hj hb
  exact paid.quote w.1 w.2 hj hb v _ hw

/-- The package's replica estimate for fixed original fields supplies the
actual matching label and its price without separate input quota data. -/
theorem fixed_grid (hC : C.Makes) {b m j D : ℕ}
    (x : I → Cover) (v : (i : I) → C.label (d i)) {cap price : ℝ}
    (paid : PriceAt C cap price D d v b m j) (shape : Plot C b m j x) :
    Stamped C m j b d x v f D cap price := by
  apply grid_capture hC x v shape
  exact Eventually.of_forall fun w hj hb => paid.quote w.1 w.2 hj hb _

/-- Unconditional native prices for each fixed independent tuple of original
fields on separated three-height grids. The four-dimensional copy volume
and input dimensions both occur in the rate. -/
theorem fixed_stamps {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : (i : I) → C.label (d i))
    {a h c : ℝ} {b m j : α → ℕ} (hb : Height C.S l T b h)
    (hm : Height C.S l T m a) (hj : Height C.S l T j c) (ha : h < a) (hc : a < c) :
    let load := ((∑ i, d i : ℕ) : ℝ) * c + 4 * (Fintype.card I : ℝ) * (c - a)
    ∃ g o : α → ℝ, RateIs l T g (load - D * a) ∧
      RateLE l T o (-(((D : ℝ) + 1 / 16) * (a - h) - load)) ∧ (∀ᶠ t in l, 0 < o t) ∧
      ∀ᶠ t in l, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
        Stamped C (m t) (j t) (b t) d x v f D (g t) (o t) := by
  obtain ⟨_, _, _, L⟩ := facility.costlier
  obtain ⟨g, o, hg, ho, hpos, hp⟩ := funding anchor facility.simpleGate L.toPackage
    F.room.cutoff d v D hb hm hj hT ha hc (height_room hb hm hT ha _)
  exact ⟨g, o, hg, ho, hpos, hp.mono fun t ht x hx => fixed_grid F.room.cutoff x v ht hx⟩

/-- The OPE facilities on this Final buy the regulated multipoint matching
label on every accessible separated grid. The input ceilings and all constants
are chosen before the grid positions and the independent original fields. -/
theorem funded_stamps {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (Q : α → I → ℝ)
    {a h : ℝ} {b m j : α → ℕ} (hb : Height C.S l T b h)
    (hm : Height C.S l T m a) (hj : Height C.S l T j a) (ha : h < a)
    (hwindow : ∀ᶠ i in l, m i + 1 < j i)
    (hratio : ValueStamp l T (fun i => C.S.a (j i) / C.S.a (m i)))
    (hQ : ∀ s, ValueStamp l T (fun i => Q i s)) :
    ∃ g o : α → ℝ, ValueStamp l T g ∧
      RateLE l T o (-(((D : ℝ) + 1 / 16) * (a - h) - ((∑ i, d i : ℕ) : ℝ) * a)) ∧
      ∀ᶠ t in l, ∀ (x : I → Cover) (v : (i : I) → C.label (d i)),
        Plot C (b t) (m t) (j t) x →
        (∀ i, ∀ᶠ w : ℕ × ℕ in f.fuse, Next.UVStress.quota C (d i) (j t) w.1 w.2
          (v i) ≤ Q t i) →
        Stamped C (m t) (j t) (b t) d x v f D
          (g t * C.S.a (m t) ^ D / C.S.a (j t) ^ (∑ i, d i)) (o t) := by
  obtain ⟨_, _, _, L⟩ := facility.costlier
  obtain ⟨g, o, hg, ho, hpaid⟩ := cost_funding L facility.simpleGate anchor hT Q d D
    hb hm hj ha hwindow hratio F.room.cutoff hQ
  refine ⟨g, o, hg, ho, hpaid.mono ?_⟩
  intro t ht x v hs hv
  exact capture_on_grid F.room.cutoff x v ht hs hv

open MeasureTheory Marker Extraction MergeProof.Accent MergeProof.Replicum OPE.Therm OPE.Cards
open WilsonWholeLimit EngineeringWeightedReadout

/-- A common local price pays every exterior detector row at its native level.
The exterior banks can be chosen before the central location, regulator,
frame, input fields, candidate, and buffer-level price. -/
theorem paid_columns (F : Spec.Final C f S) {D : ℕ} (U : Detector S D)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ b₀ : ℕ, ∃ n : Fin U.size → ℕ, ∃ B : (i : Fin U.size) → Fin (U.listen i).length → ℝ,
      (∀ i j, 0 ≤ B i j) ∧ ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ b : ℕ, b₀ ≤ b →
      ∀ (A : ℝ → PhysMS.tower S) (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ)
        (x : I → E4) (z : S.Field D) (a : ℝ),
        PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) a (detectorCentral A v r x z w.1 w.2) →
        ‖wholeReadout U A r (fun i => moment (C.beta w.1 w.2)
          (detectorDiscrepancy A U v r x z w.1 w.2 i))‖ ≤
          columnPrice (wholeReadout U A r) (fun i => a *
            ∏ j, (B i j * C.S.a (n i) ^ (-((OPE.tags S (U.listen i) j).1 : ℝ) - δ) + 1)) := by
  let dE (i : Fin U.size) (j : Fin (U.listen i).length) := (OPE.tags S (U.listen i) j).1
  let e (i : Fin U.size) (j : Fin (U.listen i).length) : C.label (dE i j) :=
    S.representative _ (OPE.tags S (U.listen i) j).2
  let R (i : Fin U.size) (j : Fin (U.listen i).length) : ℝ := 1 + ‖e i j‖
  have hR (i : Fin U.size) (j : Fin (U.listen i).length) : 0 < R i j :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have sep (i : Fin U.size) : Injective (Sum.elim (fun _ : Unit => (0 : E4))
      (OPE.positions S (U.listen i)).ofLp) :=
    (consIn 0 (OPE.positions S (U.listen i)).ofLp (e := Equiv.refl _)).mp
      (generic_conf _ (U.awake i))
  choose t ht q hq n hqn B hB H using fun i : Fin U.size =>
    complete_readout (arity := Fintype.card I) F (dE i) (R i) (hR i) δ hδ
      (OPE.positions S (U.listen i)).ofLp (sep i) 0 0
  refine ⟨Finset.univ.sup q, n, B, hB, ?_⟩
  filter_upwards [eventually_all.mpr H, (Cards.largeMesh f).eventually_ge_atTop (C.ref 0)]
    with w hw hunit
  intro b hb A v r x z a hp
  apply column_bound
  intro i
  have he (j : Fin (U.listen i).length) : ‖e i j‖ ≤ R i j := le_add_of_nonneg_left zero_le_one
  have hc : PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) a (central w.1 w.2
      (paddedLabels C 0 (OPE.Orbits.names (PhysMS.Frame.born A r v)))
      (OPE.detectorRaw S ⟨D, z⟩) (paddedPositions x)) := by
    rw [padded_central F.room.cutoff 0 hunit]
    exact hp
  have h := hw i b ((Finset.le_sup (s := Finset.univ) (f := q) (Finset.mem_univ i)).trans hb)
    hp.live (e i) he (paddedLabels C 0 (OPE.Orbits.names (PhysMS.Frame.born A r v)))
    (OPE.detectorRaw S ⟨D, z⟩) (paddedPositions x) a hc 0 0 hunit w.1 le_rfl
  change ‖∫ W, (actualSignedTransport C (N := w.1)
      (detectorNumerator A U v r x z w.1 w.2 0 0 i) le_rfl W).part
      (Stock.final (Region (Fin (U.listen i).length))) ∂scene C.path w.1 w.2 w.1‖ ≤ _ at h
  rw [normalized_detector F.room.cutoff 0 0 hunit] at h
  exact h

/-- On the original ordered regulator tail, one matching label pays all rows
of the mixed physical readout, for every candidate simultaneously. -/
theorem stamped_readout (F : Spec.Final C f S) {D : ℕ} (U : Detector S D)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ b₀ : ℕ, ∃ n : Fin U.size → ℕ, ∃ E : (i : Fin U.size) → Fin (U.listen i).length → ℝ,
      ∃ B : ℝ, (∀ i j, 0 ≤ E i j) ∧ 0 ≤ B ∧
      ∀ (J : ℝ → PhysMS.tower S) (r : ℝ) (v : ∀ i, (Climb.Bel C.book).Field (d i))
        (x : I → Cover),
      ∀ b, b₀ ≤ b → ∀ (m j : ℕ) (cap price : ℝ),
        Stamped C m j b d x (fun i => S.representative _ (PhysMS.Frame.born J r v i))
          f D cap price → ∀ η : ℝ, 0 < η →
        ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse,
          m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (Z w) ≤ cap ∧
          ∀ z : S.Field D,
          ‖wholeReadout U J r (fun i => moment (C.beta w.1 w.2)
            (detectorDiscrepancy J U v r (fun a => C.S.gridPoint j (x a)) z w.1 w.2 i))‖ ≤
            columnPrice (wholeReadout U J r) (fun i =>
              (price + ‖Z w - S.representative D z‖ * (B * C.S.a b ^ (-(D : ℝ) - δ) + η)) *
              ∏ k, (E i k * C.S.a (n i) ^ (-((OPE.tags S (U.listen i) k).1 : ℝ) - δ) + 1)) := by
  obtain ⟨b₁, _, B, hB, H₁⟩ := stamped_candidates (d := d) F D δ hδ
  obtain ⟨b₂, n, E, hE, H₂⟩ := paid_columns (d := d) F U δ hδ
  refine ⟨max b₁ b₂, n, E, B, hE, hB, ?_⟩
  intro J r v x b hb m j cap price hs η hη
  obtain ⟨Z, hZ⟩ := H₁ J r v x b ((le_max_left ..).trans hb) m j cap price hs η hη
  refine ⟨Z, ?_⟩
  filter_upwards [hZ, H₂] with w hw hg
  obtain ⟨hlive, hm, hcap, hp⟩ := hw
  refine ⟨hm, hcap, fun z => hg b ((le_max_right ..).trans hb) J v r _ z _ ?_⟩
  exact ⟨hlive, (hp z).1, (hp z).2⟩

end YM.Integration.StampedPhysicalDetector
