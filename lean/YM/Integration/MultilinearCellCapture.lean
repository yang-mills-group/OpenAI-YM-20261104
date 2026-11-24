import YM.Integration.StampedPhysicalDetector

/-! Original multipoint capture for a finite basis and its full multilinear
expansion. All basis tuples use one regulator tail and each signed difference
is combined before the cell norm. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MultilinearCellCapture
open Function Filter Lattice Wilson RG Cells Extra.Histories Frontier6.Road
open OPE StampedPhysicalDetector
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {I : Type} [Fintype I] {d : I → ℕ}

private theorem quota_sum {A : Type} [Fintype A] {D m N p : ℕ} (hC : C.Makes)
    (hm : C.ref D ≤ m) (hN : m ≤ N) (q : A → C.label D) (c : A → ℂ) :
    Next.UVStress.quota C D m N p (∑ t, c t • q t) ≤
      ∑ t, ‖c t‖ * Next.UVStress.quota C D m N p (q t) := by
  let L := (((hC.calibrated D N p (hm.trans hN)).linear m hm hN).1.mk' _).comp
    (C.factory D N p).terminal.symm.toLinearMap
  change (C.labels.level D).coeffSize (L (∑ t, c t • q t)) ≤
    ∑ t, ‖c t‖ * (C.labels.level D).coeffSize (L (q t))
  rw [map_sum]
  simp only [map_smul]
  exact (Size.finite _ Finset.univ (fun t => c t • L (q t))).trans_eq
    (by simp only [Size.smul])

/-- The same finite profile estimate for a specified bank of true regulated
labels. This retains the labels of any previously purchased source. -/
theorem profile_selected {A : Type} [Fintype A] {D m j b : ℕ} (hC : C.Makes)
    (hm : C.ref D ≤ m) (x : A → I → Cover) (u : A → (i : I) → C.label (d i))
    (c : A → ℂ) (cap price : A → ℝ)
    (Z : A → (ℕ × ℕ) → C.label D)
    (hZ : ∀ t, ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
      m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (Z t w) ≤ cap t ∧
      Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d (x t) (u t) w.1 w.2 (Z t w)) ∧
      (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2)
        (leafGap C j D d (x t) (u t) w.1 w.2 (Z t w)) ≤ price t) :
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
      m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (∑ t, c t • Z t w) ≤ (∑ t, ‖c t‖ * cap t) ∧
      let gap := (∑ t, c t • leaves C j d (x t) (u t) w.1 w.2) - C.O w.1 w.2 (∑ t, c t • Z t w) 0
      let cell := center C.S w.2 hb 0
      Interior (cell.chamber 0) gap ∧
        cell.rootTest (C.beta w.1 w.2) gap ≤ (∑ t, ‖c t‖ * price t) := by
  let combined (w : ℕ × ℕ) : C.label D := ∑ t, c t • Z t w
  filter_upwards [eventually_all.mpr hZ, (OPE.Cards.largeMesh f).eventually_ge_atTop (max m b)]
    with w hw hcut
  have hm' : m ≤ w.1 := (le_max_left ..).trans hcut
  have hb : b ≤ w.1 := (le_max_right ..).trans hcut
  let T := center C.S w.2 hb 0
  let A' (t : A) := leafGap C j D d (x t) (u t) w.1 w.2 (Z t w)
  have hp (t : A) : Next.UVStress.quota C D m w.1 w.2 (Z t w) ≤ cap t ∧
      Interior (T.chamber 0) (A' t) ∧ T.rootTest (C.beta w.1 w.2) (A' t) ≤ price t :=
    (hw t).choose_spec.2
  have hcounter : C.O w.1 w.2 (combined w) 0 = ∑ t, c t • C.O w.1 w.2 (Z t w) 0 := by
    let L := (C.linearO w.1 w.2 D 0).mk' _
    change L (∑ t, c t • Z t w) = ∑ t, c t • L (Z t w)
    rw [map_sum]
    simp only [map_smul]
  have hsum : (∑ t, c t • leaves C j d (x t) (u t) w.1 w.2) - C.O w.1 w.2 (combined w) 0 =
      ∑ t, c t • A' t := by
    simp only [leafGap, A', hcounter, smul_sub, Finset.sum_sub_distrib]
  have hroot := Next.UVStress.root_sum T (C.beta w.1 w.2) Finset.univ A' c
    (fun t _ => (hp t).2.1) (Cells.seamless hC w.1 w.2)
  refine ⟨hb, hm', (quota_sum hC hm hm' _ c).trans (Finset.sum_le_sum (fun t _ =>
    mul_le_mul_of_nonneg_left (hp t).1 (norm_nonneg _))), ?_, ?_⟩
  · rw [hsum]
    exact hroot.1
  · rw [hsum]
    exact hroot.2.trans (Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hp t).2.2 (norm_nonneg _))

/-- A finite joint profile can couple all original insertion locations.
The certified label is its signed weighted sum. Every reflected copy sees
the complete profile, at the absolute-weighted sum of native cell costs. -/
theorem profile {A : Type} [Fintype A] {D m j b : ℕ} (hC : C.Makes)
    (hm : C.ref D ≤ m) (x : A → I → Cover) (u : A → (i : I) → C.label (d i))
    (c : A → ℂ) (cap price : A → ℝ)
    (hs : ∀ t, Stamped C m j b d (x t) (u t) f D (cap t) (price t)) :
    ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
      m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (Z w) ≤ (∑ t, ‖c t‖ * cap t) ∧
      let gap := (∑ t, c t • leaves C j d (x t) (u t) w.1 w.2) - C.O w.1 w.2 (Z w) 0
      let cell := center C.S w.2 hb 0
      Interior (cell.chamber 0) gap ∧
        cell.rootTest (C.beta w.1 w.2) gap ≤ (∑ t, ‖c t‖ * price t) := by
  choose Z hZ using fun t => (hs t).probe
  exact ⟨_, profile_selected hC hm x u c cap price Z hZ⟩

/-- Combine original signed cells at the raw-label level. Their native quotas
and reflected prices both obey the same absolute-coefficient sum. -/
theorem combine {A : Type} [Fintype A] {D m j b : ℕ} (hC : C.Makes)
    (hm : C.ref D ≤ m) (x : I → Cover) (v : (i : I) → C.label (d i))
    (u : A → (i : I) → C.label (d i)) (c : A → ℂ) (cap price : A → ℝ)
    (he : ∀ N p, leaves C j d x v N p = ∑ t, c t • leaves C j d x (u t) N p)
    (hs : ∀ t, Stamped C m j b d x (u t) f D (cap t) (price t)) :
    Stamped C m j b d x v f D (∑ t, ‖c t‖ * cap t) (∑ t, ‖c t‖ * price t) := by
  obtain ⟨Z, hZ⟩ := profile hC hm (fun _ : A => x) u c cap price hs
  refine ⟨Z, hZ.mono ?_⟩
  intro w hw
  obtain ⟨hb, hm', hcap, hi, hprice⟩ := hw
  exact ⟨hb, hm', hcap, by rwa [leafGap, he], by rwa [leafGap, he]⟩

abbrev Indices (C : Family G) (d : I → ℕ) := (i : I) → (C.labels.level (d i)).Index

def basisLabels (q : Indices C d) (i : I) : C.label (d i) := Pi.single (q i) 1

def weight (v : (i : I) → C.label (d i)) (q : Indices C d) : ℂ := ∏ i, v i (q i)

/-- The exact independent-input expansion holds as a function on configurations,
before signed subtraction, moments, or norms. -/
theorem leaves_expansion (j N p : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i)) :
    leaves C j d x v N p = ∑ q : Indices C d, weight v q • leaves C j d x (basisLabels q) N p := by
  funext U
  let field (i : I) := (C.linearO N p (d i) (Cells.location C.S j N p (x i))).mk' _
  have hv (i : I) : v i = ∑ t, (v i t) • (Pi.single t (1 : ℂ)) := by
    funext h
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have hfield (i : I) : (field i (v i)) U =
      ∑ t, v i t * (field i (Pi.single t (1 : ℂ))) U := by
    have he := congrFun (congrArg (field i) (hv i)) U
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he
  simp only [leaves, Finset.sum_apply, Finset.prod_apply, Pi.smul_apply, smul_eq_mul]
  change (∏ i, (field i (v i)) U) =
    ∑ q : Indices C d, weight v q * (∏ i, (field i (basisLabels q i)) U)
  simp only [hfield, Fintype.prod_sum, Finset.prod_mul_distrib, basisLabels, weight]

/-- For every original input tuple the same finite basis bank gives the
actual matching label. The inputs may vary arbitrarily with the outer
scale, grid configuration or frame. Each basis row has the native rate. -/
theorem funded_basis_bank {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) {a h c : ℝ} {b m j : α → ℕ}
    (hb : Height C.S l T b h) (hm : Height C.S l T m a) (hj : Height C.S l T j c)
    (ha : h < a) (hc : a < c) :
    let load := ((∑ i, d i : ℕ) : ℝ) * c + 4 * (Fintype.card I : ℝ) * (c - a)
    ∃ gain error : α → Indices C d → ℝ,
      (∀ u, RateIs l T (fun t => gain t u) (load - D * a) ∧
        RateLE l T (fun t => error t u) (-(((D : ℝ) + 1 / 16) * (a - h) - load))) ∧
      ∀ᶠ t in l, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
        ∀ v : (i : I) → C.label (d i), Stamped C (m t) (j t) (b t) d x v f D
          (∑ u, ‖weight v u‖ * gain t u) (∑ u, ‖weight v u‖ * error t u) := by
  choose gain error hg he hpos H using fun u : Indices C d =>
    fixed_stamps F facility anchor hT D (basisLabels u) hb hm hj ha hc
  refine ⟨fun t u => gain u t, fun t u => error u t, fun u => ⟨hg u, he u⟩, ?_⟩
  filter_upwards [eventually_all.mpr H, hm.grows.eventually_ge_atTop (C.ref D)]
    with t ht href
  intro x hx v
  exact combine F.room.cutoff href x v basisLabels (weight v) _ _
    (fun N p => leaves_expansion (j t) N p x v) (fun u => ht u x hx)

/-- The rate of the whole bank is the sum of the individual input rates and
the error rate of each finite basis cell. -/
theorem weighted_rate {α : Type*} {l : Filter α} {T : α → ℝ} (hT : Tendsto T l atTop)
    (v : α → (i : I) → C.label (d i)) (price : α → Indices C d → ℝ) (κ : I → ℝ) (R : ℝ)
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (κ i))
    (hp : ∀ u, RateLE l T (fun t => price t u) R) :
    RateLE l T (fun t => ∑ u, ‖weight (v t) u‖ * price t u) ((∑ i, κ i) + R) :=
  RateLE.sum hT fun u _ =>
    (RateLE.prod (S := Finset.univ) hT (fun i _ => hv i (u i))).norm.mul (hp u)

/-- Positive room for the full product degree, after normalizing each leaf
at its own engineering dimension. -/
theorem engineering_margin (D σ n : ℕ) :
    ∃ h a c : ℝ, 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      D + (1 : ℝ) / 32 ≤
        ((D : ℝ) + 1 / 16) * (a - h) - σ * c - 4 * n * (c - a) + σ := by
  let M : ℝ := 1 + 2 * D + σ + 8 * n
  have hM : 1 ≤ M := by dsimp [M]; norm_cast; omega
  let s : ℝ := (1 / 64) / M
  have hs : 0 < s := div_pos (by norm_num) (zero_lt_one.trans_le hM)
  have hsmall : s ≤ 1 / 64 := div_le_self (by norm_num) hM
  have hsM : s * M = 1 / 64 := div_mul_cancel₀ _ (zero_lt_one.trans_le hM).ne'
  have hcost : s * (2 * D + σ + 8 * n + 1 / 8) ≤ s * M := by
    apply mul_le_mul_of_nonneg_left _ hs.le
    dsimp [M]
    linarith
  exact ⟨s, 1 - s, 1 + s, hs, by linarith only [hsmall], by linarith only [hs],
    by linarith only [hs], by nlinarith only [hcost, hsM]⟩

/-- The same funded Wilson run admits levels and an actual matching label
whose complete signed cell price beats the horizon power on every late
admitted grid, for inputs carrying their engineering powers. -/
theorem engineering_stamps {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (-(d i : ℝ))) :
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ cap price : α → ℝ, RateLE l T price (-(D : ℝ) - 1 / 32) ∧
        ∀ᶠ t in l, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
          Stamped C (m t) (j t) (b t) d x (v t) f D (cap t) (price t) := by
  obtain ⟨h, a, c, hh, ha, h₁, hc, hmargin⟩ :=
    engineering_margin D (∑ i, d i) (Fintype.card I)
  obtain ⟨b, hb⟩ := found hT C.path.levels.fits.mesh hh.le
  obtain ⟨m, hm⟩ := found hT C.path.levels.fits.mesh (hh.trans ha).le
  obtain ⟨j, hj⟩ := found hT C.path.levels.fits.mesh (zero_lt_one.trans hc).le
  obtain ⟨g, e, hr, hs⟩ := funded_basis_bank (d := d) F facility anchor hT D hb hm hj ha
    (h₁.trans hc)
  refine ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, h₁, hc, _, _, ?_,
    hs.mono (fun t ht x hx => ht x hx (v t))⟩
  apply (weighted_rate hT v e (fun i => -(d i : ℝ)) _ hv (fun u => (hr u).2)).mono
  push_cast at hmargin ⊢
  rw [Finset.sum_neg_distrib]
  linarith only [hmargin]

/-- At the chosen three engineering scales, all finite joint test profiles
are paid on one outer-scale tail. Their cardinality and the full joint
weights may vary at every scale. -/
theorem engineering_profiles {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (-(d i : ℝ))) :
    ∃ b m j : α → ℕ, ∃ cap price : α → ℝ, RateLE l T price (-(D : ℝ) - 1 / 32) ∧
      ∀ᶠ t in l, ∀ (K : Type) [Fintype K], ∀ (x : K → I → Cover) (c : K → ℂ),
        (∀ e, Plot C (b t) (m t) (j t) (x e)) →
        ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b t ≤ w.1,
          m t ≤ w.1 ∧ Next.UVStress.quota C D (m t) w.1 w.2 (Z w) ≤ (∑ e, ‖c e‖) * cap t ∧
          let gap := (∑ e, c e • leaves C (j t) d (x e) (v t) w.1 w.2) - C.O w.1 w.2 (Z w) 0
          let cell := center C.S w.2 hb 0
          Interior (cell.chamber 0) gap ∧ cell.rootTest (C.beta w.1 w.2) gap ≤
            (∑ e, ‖c e‖) * price t := by
  obtain ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, h₁, hc, cap, price, hprice, hp⟩ :=
    engineering_stamps F facility anchor hT D v hv
  refine ⟨b, m, j, cap, price, hprice, ?_⟩
  filter_upwards [hp, hm.grows.eventually_ge_atTop (C.ref D)] with t ht href
  intro K _ x u hx
  simpa only [Finset.sum_mul] using profile F.room.cutoff href x (fun _ => v t) u
    (fun _ => cap t) (fun _ => price t) (fun e => ht (x e) (hx e))

omit [Fintype I] in
/-- Actual raw local tensor coordinates of dimensionally rescaled independent
fields satisfy the input side of `engineering_stamps`. -/
theorem scaled_input_rate {α : Type*} {l : Filter α} {T : α → ℝ}
    (hT : Tendsto T l atTop) (v : (i : I) → C.label (d i)) (i : I)
    (k : (C.labels.level (d i)).Index) :
    RateLE l T (fun t =>
      ((Real.exp (-(d i : ℝ) * T t) : ℂ) • v i) k) (-(d i : ℝ)) := by
  have h : RateLE l T (fun t => Real.exp (-(d i : ℝ) * T t) * ‖v i k‖) (-(d i : ℝ)) := by
    simpa only [add_zero] using (RateLE.exp (-(d i : ℝ)) hT).mul (RateLE.const ‖v i k‖ hT)
  apply h.transfer
  filter_upwards with t
  change ‖((Real.exp (-(d i : ℝ) * T t) : ℝ) : ℂ) * v i k‖ ≤
    ‖Real.exp (-(d i : ℝ) * T t) * ‖v i k‖‖
  simp only [norm_mul, Complex.norm_real, norm_norm, le_refl]

/-- The native positive power margin pays every finite inverse-coupling
order after the horizon engineering power is restored. -/
theorem all_loop_orders {α : Type*} {l : Filter α} {T : α → ℝ}
    (hT : Tendsto T l atTop) (D : ℕ) (price : α → ℝ)
    (hprice : RateLE l T price (-(D : ℝ) - 1 / 32)) {j : α → ℕ} {c : ℝ}
    (hj : Height C.S l T j c) (n : ℕ) :
    Tendsto (fun t => C.path.levels.clock.hatBeta (j t) ^ n *
      (Real.exp ((D : ℝ) * T t) * price t)) l (𝓝 0) := by
  have hβ := ((OPE.Log.betaStamp (C := C) hT hj).zeroCost hT).pays hT
  exact ((hβ.pow n hT).mul ((RateLE.exp (D : ℝ) hT).mul hprice)).tends
    (by simp only [mul_zero, zero_add]; linarith) hT

open WilsonWholeLimit EngineeringWeightedReadout

/-- The funded basis and exterior Gram banks jointly price the original full
readout, uniformly over the running physical frame, arbitrary independent
inputs, grid, and candidate. The only remaining candidate-dependent term
is the actual cutoff counterlabel difference. -/
theorem funded_readout {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) {D : ℕ} (U : Detector S D) (δ : ℝ) (hδ : 0 < δ)
    {a h c : ℝ} {b m j : α → ℕ} (hb : Height C.S l T b h)
    (hm : Height C.S l T m a) (hj : Height C.S l T j c) (ha : h < a) (hc : a < c) :
    let load := ((∑ i, d i : ℕ) : ℝ) * c + 4 * (Fintype.card I : ℝ) * (c - a)
    ∃ n : Fin U.size → ℕ, ∃ E : (i : Fin U.size) → Fin (U.listen i).length → ℝ,
      ∃ B : ℝ, ∃ gain error : α → Indices C d → ℝ, (∀ i j, 0 ≤ E i j) ∧ 0 ≤ B ∧
      (∀ u, RateIs l T (fun t => gain t u) (load - D * a) ∧
        RateLE l T (fun t => error t u) (-(((D : ℝ) + 1 / 16) * (a - h) - load))) ∧
      ∀ᶠ t in l, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
        ∀ (A : ℝ → PhysMS.tower S) (r : ℝ) (v : ∀ i, (Climb.Bel C.book).Field (d i))
          (η : ℝ), 0 < η →
        let wgt := weight (fun i => S.representative _ (PhysMS.Frame.born A r v i))
        ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse, m t ≤ w.1 ∧
          Next.UVStress.quota C D (m t) w.1 w.2 (Z w) ≤ (∑ u, ‖wgt u‖ * gain t u) ∧
          ∀ z : S.Field D,
          ‖wholeReadout U A r (fun i => moment (C.beta w.1 w.2) (detectorDiscrepancy
            A U v r (fun k => C.S.gridPoint (j t) (x k)) z w.1 w.2 i))‖ ≤
            columnPrice (wholeReadout U A r) (fun i =>
              ((∑ u, ‖wgt u‖ * error t u) + ‖Z w - S.representative D z‖ *
                (B * C.S.a (b t) ^ (-(D : ℝ) - δ) + η)) *
              ∏ k, (E i k * C.S.a (n i) ^ (-((OPE.tags S (U.listen i) k).1 : ℝ) - δ) + 1)) := by
  obtain ⟨b₀, n, E, B, hE, hB, H⟩ := stamped_readout (d := d) F U δ hδ
  obtain ⟨gain, error, hrate, hprice⟩ :=
    funded_basis_bank (d := d) F facility anchor hT D hb hm hj ha hc
  refine ⟨n, E, B, gain, error, hE, hB, hrate, ?_⟩
  filter_upwards [hprice, hb.grows.eventually_ge_atTop b₀] with t hpay hlevel
  intro x hx A r v η hη
  exact H A r v x (b t) hlevel (m t) (j t) _ _ (hpay x hx _) η hη

end YM.Integration.MultilinearCellCapture
