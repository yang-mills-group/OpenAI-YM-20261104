import YM.Integration.FundedIntrinsicReadout

/-! The original replicated root test using the terminal label of the
canonical intrinsic report of the complete Wilson product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicPhysicalCell
open Function Filter Lattice Wilson RG Cells OPE OPE.Log MergeProof Frontier6.Road
open MultilinearCellCapture FundedIntrinsicReadout Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ}

/-- Conversion from the measured germ at `b` to the actual terminal label. -/
def chart (C : Family G) (D b : ℕ) : ℝ :=
  2 * Columns.juice C.path.levels b * (C.S.a (C.ref D) / C.S.a b)^D

theorem chart_nonneg (C : Family G) (D b : ℕ) : 0 ≤ chart C D b :=
  mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans (Columns.juice_pos ..)))
    (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)

theorem terminal_cost (facility : Facilities C f S) (H : C.Makes) (D N p b : ℕ)
    (ho : Opened C D b p) (hn : b ≤ N) (y : C.label D) :
    ‖(C.factory D N p).terminal y‖ ≤ chart C D b * mCost C D N p b y := by
  obtain ⟨_,_,_,_,base⟩ := facility.along
  have hq : Next.UVStress.quota C D b N p ((C.factory D N p).terminal y) ≤
      2 * mCost C D N p b y := by
    unfold Next.UVStress.quota
    rw [LinearEquiv.symm_apply_apply]
    exact (size_gap D N p b H ho hn y).2
  apply (Columns.whole_origin base _ ho.post hn).trans
  have hpos := mul_nonneg (zero_le_one.trans (Columns.juice_pos C.path.levels b))
    (pow_nonneg (div_nonneg (C.S.a_pos (C.ref D)).le (C.S.a_pos b).le) D)
  exact (mul_le_mul_of_nonneg_left hq hpos).trans_eq (by unfold chart; ring)

theorem chart_rate {α : Type*} {l : Filter α} {T : α → ℝ} (hT : Tendsto T l atTop)
    (D : ℕ) {b : α → ℕ} {h : ℝ} (hb : Height C.S l T b h) :
    RateIs l T (fun t => chart C D (b t)) ((D:ℝ)*h) := by
  have hj := Columns.juice_rate_seq C hb.grows hb.pace
  have ha := ((RateIs.const hT (C.S.a_pos (C.ref D))).div hb.mesh).power D
  simpa only [chart, zero_add, zero_sub, neg_neg] using
    ((RateIs.const hT (by norm_num : (0:ℝ) < 2)).mul hj).mul ha

/-- The subtraction is exactly the canonical operator in the original
terminal frame. The original normalized full pushed density is booked. -/
def Observed (H : C.Makes) (b j D : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (w : ℕ × ℕ) (fee : ℝ) : Prop :=
  ∃ (ho : Opened C D b w.2) (live : b ≤ w.1),
    let field := leaves C j d x v w.1 w.2
    let label := (C.factory D w.1 w.2).terminal (topReport C w.1 w.2 D H b ho live field)
    let gap := leafGap C j D d x v w.1 w.2 label
    Booked C w.1 w.2 D field b live ∧ Interior ((center C.S w.2 live 0).chamber 0) gap ∧
      (center C.S w.2 live 0).rootTest (C.beta w.1 w.2) gap ≤ fee

theorem Observed.weaken {H : C.Makes} {b j D : ℕ} {x : I → Cover} {v : (i : I) → C.label (d i)}
    {w : ℕ × ℕ} {e e' : ℝ} (h : Observed H b j D x v w e) (he : e ≤ e') :
    Observed H b j D x v w e' := by
  obtain ⟨ho, hl, hb, hi, hr⟩ := h
  exact ⟨ho, hl, hb, hi, hr.trans he⟩

/-- Spend the measured error in the uniform physical one-point bank at
the same cutoff and on the same central cell. -/
theorem canonical (F : Spec.Final C f S) (facility : Facilities C f S)
    {b m j D : ℕ} {x : I → Cover} {v : (i : I) → C.label (d i)}
    {cap fee paid bill : ℝ} {w : ℕ × ℕ} {Z : Indices C d → C.label D}
    (h : Full F.room.cutoff b m j D x v cap fee paid w Z)
    (hn : b ≤ w.1) (hb : 0 ≤ bill) (bank : ∀ z : C.label D,
      Interior ((center C.S w.2 hn 0).chamber 0) (C.O w.1 w.2 z 0) ∧
      (center C.S w.2 hn 0).rootTest (C.beta w.1 w.2) (C.O w.1 w.2 z 0) ≤ ‖z‖ * bill) :
    Observed F.room.cutoff b j D x v w (fee + chart C D b * bill * paid) := by
  obtain ⟨ho, hs, hf, booked, _, hwrap, _, localGap, rootGap⟩ := h
  let field := leaves C j d x v w.1 w.2
  let T := C.factory D w.1 w.2
  let reported := topReport C w.1 w.2 D F.room.cutoff b ho hn field
  let z := ∑ u, weight v u • Z u
  let candidate := T.terminal reported
  have hr : mCost C D w.1 w.2 b (reported - T.terminal.symm z) ≤ paid := hwrap
  have hn' := terminal_cost facility F.room.cutoff D w.1 w.2 b ho hn (reported - T.terminal.symm z)
  have hnorm : ‖z-candidate‖ ≤ chart C D b * paid := by
    change ‖z - T.terminal reported‖ ≤ _
    rw [norm_sub_rev]
    rw [map_sub, LinearEquiv.apply_symm_apply] at hn'
    exact hn'.trans (mul_le_mul_of_nonneg_left hr (chart_nonneg ..))
  let E := C.O w.1 w.2 (z-candidate) 0
  have equation : leafGap C j D d x v w.1 w.2 candidate = leafGap C j D d x v w.1 w.2 z + E := by
    unfold E leafGap
    rw [show C.O w.1 w.2 (z-candidate) 0 = C.O w.1 w.2 z 0 - C.O w.1 w.2 candidate 0 from
      ((C.linearO w.1 w.2 D 0).mk' _).map_sub _ _]
    abel
  obtain ⟨localE,rootE⟩ := bank (z-candidate)
  have rootError : (center C.S w.2 hn 0).rootTest (C.beta w.1 w.2) E ≤ chart C D b * bill * paid :=
    rootE.trans ((mul_le_mul_of_nonneg_right hnorm hb).trans_eq (by ring))
  refine ⟨ho, hn, booked, ?_, ?_⟩
  · change Interior _ (leafGap C j D d x v w.1 w.2 candidate)
    rw [equation]
    exact localGap.plus localE
  · change (center C.S w.2 hn 0).rootTest _ (leafGap C j D d x v w.1 w.2 candidate) ≤ _
    rw [equation]
    exact ((Cells.seamless F.room.cutoff w.1 w.2).semi _ _ _ localGap localE).trans
      (add_le_add rootGap rootError)

/-- The original signed multipoint residual at its canonical intrinsic
counterterm has the full engineering exponent and a strict fractional margin. -/
theorem engineering {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (-(d i : ℝ))) :
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ fee : α → ℝ, RateLE l T fee (-(D:ℝ)-1/32) ∧
        ∀ᶠ t in l, ∀ (x : I → Cover), Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
          Observed F.room.cutoff (b t) (j t) D x (v t) w (fee t) := by
  obtain ⟨b₀, _, B, hB, bank⟩ := StampedPhysicalDetector.label_bound F D 1 one_pos
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,hc,cap,e,Z,he,hfull⟩ :=
    FundedIntrinsicReadout.engineering F facility anchor hT D v hv
  let q := -(D:ℝ)-1/32
  let s := q-D*h-((D:ℝ)+1)*h-1
  let bill (t : α) := B * C.S.a (b t) ^ (-(D:ℝ)-1) + 1
  have hfirst := (RateLE.const B hT).mul ((hb.mesh.rpow (-(D:ℝ)-1)).pays hT)
  have hbill : RateLE l T bill (((D:ℝ)+1)*h) := by
    apply RateLE.add (F:=fun t => B*C.S.a (b t)^(-(D:ℝ)-1)) (F':=fun _ => 1) _ _ hT
    · apply hfirst.mono; linarith
    · apply (RateLE.const (1:ℝ) hT).mono
      positivity
  have rate := ((chart_rate hT D hb |>.pays hT).mul hbill).mul (RateIs.exp s hT |>.pays hT)
  have hs : (D:ℝ)*h + ((D:ℝ)+1)*h + s < q := by dsimp [s]; linarith
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,hc,fun t => e t + Real.exp (q*T t),
    he.add (RateIs.exp q hT |>.pays hT) hT, ?_⟩
  filter_upwards [hfull s,hb.grows.eventually_ge_atTop b₀,rate q hs] with t paid hbase cash
  intro x hx
  filter_upwards [paid x hx, bank (b t) hbase 1 one_pos] with w full voucher
  obtain ⟨hl, useLabel⟩ := voucher
  have hpos : 0 ≤ bill t := add_nonneg (mul_nonneg hB (Real.rpow_nonneg (C.S.a_pos _).le _)) zero_le_one
  exact (canonical F facility full hl hpos (fun z => useLabel z 0)).weaken
    (add_le_add_right ((le_abs_self _).trans cash) _)

end YM.Integration.IntrinsicPhysicalCell
