import YM.Integration.SignedLowOutputPacket
import YM.Integration.SignedCompactWilson
import YM.Integration.OPEScalarFieldAsymptotic

/-! At output horizons zero through three, a candidate scalar times the
true unit fits the whole running field at order N precisely when it fits
the original normalized finite Wilson multipoint moment at that order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedLowOutputAsymptotic
open Function Filter Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Trace.Sundial FVA2 Pert.Position Maxwell
open Wilson PhysicalMSOPECandidate SignedTreeTransport OPEScalarAsymptotic
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {n i D : ℕ}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (hS : Services C f S) (v : Fin n → E C.labels i)
    (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n)

def original (r : ℝ) (x : Points n) (a : ℕ × ℕ) (j : ℕ) (hj : j ≤ a.1) : ℂ :=
  mean C a.1 a.2 j hj (WilsonWholeLimit.product (r • x).ofLp (Frame.born J r v) a.1 a.2)

include hS hK hsep in
theorem convergence (r : ℝ) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ a.1),
      ‖original J v r x a j hj - full F J v r x none‖ ≤ ε := by
  let y := fun x : Points n => r • x
  have hc : Continuous y := continuous_id.const_smul r
  have hs : y '' K ⊆ conf n := by
    rintro _ ⟨x,hx,rfl⟩
    exact Work.A05.smul_conf hr (hsep hx)
  let w := Orbits.names (Frame.born (d := fun _ : Fin n => i) J r v)
  filter_upwards [SignedCompactWilson.rounded_read F hS w (y '' K) (hK.image hc) hs hε] with a ha x hx j hj
  rw [original,mean_eq F.room.cutoff _ _ _ _ _ (WilsonWholeLimit.product_continuous ..),← dist_eq_norm]
  exact (ha (y x) ⟨x,hx,rfl⟩).le

include hJ hG X hR hS hK hsep in
theorem flat {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ a.1),
    ‖original J v r x a j hj - scalar F R J v r x none‖ ≤ ε*(g r)^N := by
  have h := OPEScalarAsymptotic.flat F R J hJ hG X hR v K hK hsep hg N (ε/2) (half_pos hε)
  filter_upwards [h,hg.positive,self_mem_nhdsWithin] with r he hp hr
  filter_upwards [convergence F J hS v K hK hsep r hr (mul_pos (half_pos hε) (pow_pos hp N))]
    with a ha x hx j hj
  exact (norm_sub_le_norm_sub_add_norm_sub _ (full F J v r x none) _).trans
    ((add_le_add (ha x hx j hj) (he x hx none)).trans_eq (by ring))

def finiteFit (g : ℝ → ℝ) (N : ℕ) (b : ℝ → Points n → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ (j : ℕ) (hj : j ≤ a.1),
    ‖original J v r x a j hj - b r x‖ ≤ ε*(g r)^N

include hJ hG X hR hS hK hsep in
theorem finite_iff {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ) (b : ℝ → Points n → ℂ) :
    finiteFit (f := f) J v K g N b ↔ fits K g N (scalar F R J v) (fun r x _ => b r x) := by
  constructor
  · intro h ε hε
    filter_upwards [h (ε/2) (half_pos hε),flat F R J hJ hG X hR hS v K hK hsep hg N _ (half_pos hε)]
      with r hr he
    obtain ⟨a,ha,he⟩ := (hr.and he).exists
    intro x hx p
    let z := original J v r x a 0 (Nat.zero_le a.1)
    have hz := he x hx 0 (Nat.zero_le a.1)
    rw [norm_sub_rev] at hz
    exact (norm_sub_le_norm_sub_add_norm_sub _ z _).trans
      ((add_le_add hz (ha x hx 0 (Nat.zero_le a.1))).trans_eq (by ring))
  intro h ε hε
  filter_upwards [h (ε/2) (half_pos hε),flat F R J hJ hG X hR hS v K hK hsep hg N _ (half_pos hε)]
    with r hr he
  filter_upwards [he] with a ha x hx j hj
  exact (norm_sub_le_norm_sub_add_norm_sub _ (scalar F R J v r x none) _).trans
    ((add_le_add (ha x hx j hj) (hr x hx none)).trans_eq (by ring))

def field (D : ℕ) (r : ℝ) (x : Points n) (_ : Viewers F) :=
  actualOutput (D := D) F R J v r (r • x).ofLp

include hJ hG X hR hS hK hsep in
theorem field_iff (hD : D < 4) {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ) (b : ℝ → Points n → ℂ) :
    OPEScalarFieldAsymptotic.estimates K g N (field F R J v D)
      (fun r x _ => b r x • (Climb.Bel C.book).unit D) ↔ finiteFit (f := f) J v K g N b := by
  have hu : (Climb.Bel C.book).unit D ≠ 0 := by
    intro he
    have h := congrArg (Extra.FD.writes C.labels D) he
    rw [Extra.FD.writes_unit,map_zero] at h
    exact one_ne_zero h
  rw [finite_iff F R J hJ hG X hR hS v K hK hsep hg N b,
    ← OPEScalarFieldAsymptotic.lift_iff ((Climb.Bel C.book).unit D) hu (scalar F R J v) (fun r x _ => b r x)]
  have he := SignedLowOutputPacket.actual_scalar (n := n) (i := i) F R J hJ hG X hD
  constructor
  · intro h ε hε
    filter_upwards [h ε hε,he] with r hr he x hx p
    change ‖Short.scalar F R (r • x).ofLp (Orbits.tags (Frame.born J r v)) 0 • (Climb.Bel C.book).unit D -
      b r x • (Climb.Bel C.book).unit D‖ ≤ ε*(g r)^N
    rw [← he v (r • x).ofLp]
    exact hr x hx p
  intro h ε hε
  filter_upwards [h ε hε,he] with r hr he x hx p
  rw [field,he v (r • x).ofLp]
  exact hr x hx p

include hJ hG X hR hS hK hsep in
theorem selected (hD : D < 4) (hV : ∀ a, Bid.pop (C.localSection a)) {q : MS.Land.Booked (ColorCode.wings G)}
    (M : MS.Land.MS_Data G q) (μ : ℝ) {k : ℝ} (T : PositionX.Bend.Booth k C.labels)
    (W : Pic.pass (Atoll.share C F.room.cutoff hV) hG M T)
    {H : (Climb.Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C} {P P' : ℝ → Spin.change S 4} {a d e : ℝ → ℝ}
    (hf : Trace.Target.FieldComparison F H Z P P' a d e) (j N : ℕ) :
    let V := Atoll.share C F.room.cutoff hV
    let g := fun r => OPETraceCoupling.finiteCoupling (Forge.transfer V M T μ W) j (glo P' r)
    let b := OPEScalarAsymptotic.truncation V M μ g N v
    OPEScalarFieldAsymptotic.estimates K g N (field F R J v D)
      (fun r x _ => b r x • (Climb.Bel C.book).unit D) ↔ finiteFit (f := f) J v K g N b :=
  field_iff F R J hJ hG X hR hS v K hK hsep hD
    (OPETraceCoupling.selected_trace F.room.cutoff hV M T μ hG W hf j).1 N _

end YM.Integration.SignedLowOutputAsymptotic
