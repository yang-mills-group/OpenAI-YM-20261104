import YM.Trace2.Transfer
import Solution.SelectedJets

set_option autoImplicit false
noncomputable section
namespace YM.FixedFieldMaxwell
open Filter Set Function OPE Spec Table Climb Ward Maxwell
open scoped Topology BigOperators ContDiff

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable (F : Final C f S) {n : ℕ}

/-- A compact set of distinct configurations has uniform diameter and clearance. -/
private lemma compact_room {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n) :
    ∃ M η : ℝ, 0 ≤ M ∧ 0 < η ∧ ∀ x ∈ K, ∀ r : ℝ, 0 < r →
      WithinRoom r M η (r • x).ofLp 0 := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hn
  · exact ⟨0, 1, le_rfl, zero_lt_one, by simp⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := id) continuousOn_id
  have sep (i j : Fin n) : ∀ᶠ η in 𝓝[>] (0 : ℝ), i ≠ j →
      ∀ x ∈ K, η ≤ ‖x i - x j‖ := by
    by_cases hij : i = j
    · simp [hij]
    have hcont : Continuous (fun x : Points n => ‖x i - x j‖) := by fun_prop
    obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hn hcont.continuousOn
    have hpos : 0 < ‖z i - z j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => hij (hc hz e)))
    filter_upwards [(gt_mem_nhds hpos).filter_mono nhdsWithin_le_nhds] with η hs _ x hx
    exact hs.le.trans (hmin hx)
  have hs : ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ i j, i ≠ j → ∀ x ∈ K, η ≤ ‖x i - x j‖ :=
    eventually_all.mpr fun i => eventually_all.mpr (sep i)
  obtain ⟨η,hsep,hη⟩ := (hs.and (self_mem_nhdsWithin (s := Ioi 0))).exists
  refine ⟨max B 0,η,le_max_right ..,hη,fun x hx r hr => ⟨fun i => ?_,fun i j hij => ?_⟩⟩
  · change ‖r • x i - 0‖ ≤ _
    rw [sub_zero,norm_smul,Real.norm_of_nonneg hr.le, mul_comm]
    exact mul_le_mul_of_nonneg_right (((PiLp.norm_apply_le x i).trans (hB x hx)).trans (le_max_left ..)) hr.le
  · change _ ≤ ‖r • x i - r • x j‖
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (hsep i j hij x hx) hr.le

/-- Fixed fields, with their engineering powers. The same tail works for every pair
of phases, including the Wilson average, and every shape in the given compact. -/
theorem phase_bound (H : Services C f S) (d : Fin n → ℕ) (a : (i : Fin n) → S.Field (d i))
    {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x ∈ K, ∀ v w : Viewers F,
      ‖(r ^ (∑ i, d i)) •
        (S.classMoment (spectator F v) d (r • x) a -
         S.classMoment (spectator F w) d (r • x) a)‖ ≤ 2 * r ^ (1 - δ) := by
  obtain ⟨M,η,hM,hη,hroom⟩ := compact_room hK hc
  obtain ⟨P,hP⟩ := Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
  have h := one_radius F (P := P) hP H
  let p : Fin n → C.book.Token := fun i => ⟨d i, S.representative _ (a i)⟩
  have hraw : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : Points n, WithinRoom r M η z.ofLp 0 →
      ∀ v w : Viewers F, ‖observe (spectator F v) z.ofLp p -
        observe (spectator F w) z.ofLp p‖ ≤ 2 * r ^ (1 - (sigma p : ℝ) - δ) :=
    universalize (fun z => Trace.vacuum_error F P h H.simpleGate p
      (x := fun r => (z r).ofLp) (o := fun _ => 0) M η δ hM hη hδ)
  filter_upwards [self_mem_nhdsWithin (s := Ioi 0), hraw] with r hr hraw x hx v w
  have hr' : 0 < r := hr
  have hz := Work.A05.smul_conf hr' (hc hx)
  have read (v : Viewers F) : observe (spectator F v) (r • x).ofLp p =
      S.classMoment (spectator F v) d (r • x) a := by
    rw [named_fin _ (spectate F v).laws.toSymmetric _ hz, Table.read_eq]
    rfl
  have hb := hraw (r • x) (hroom x hx r hr') v w
  rw [read v, read w] at hb
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hr'.le _)]
  refine (mul_le_mul_of_nonneg_left hb (pow_nonneg hr'.le _)).trans_eq ?_
  change r ^ (∑ i, d i) * (2 * r ^ (1 - ((∑ i, d i : ℕ) : ℝ) - δ)) = _
  rw [mul_left_comm, ← Real.rpow_natCast r (∑ i, d i), ← Real.rpow_add hr']
  ring_nf

/-- The rescaled correlation of a list of fixed fields; the degrees belong to the
fields and the state only enters at evaluation. -/
def normalized (s : Viewers F) (v : Fin n → S.Tag) (r : ℝ) (x : Points n) : ℂ :=
  r ^ (∑ i, (v i).1) • S.useAt (spectator F s) (r • x) v

private def raised (v : Fin n → S.Tag) (i : Fin n) (a : Axis) : Fin n → S.Tag :=
  update v i ⟨(v i).1+1,F.sector.derivatives.deriv (v i).1 a (v i).2⟩

private lemma raised_weight (v : Fin n → S.Tag) (i : Fin n) (a : Axis) :
    (∑ l, (raised F v i a l).1) = (∑ l, (v l).1) + 1 := by
  classical
  have split (l : Fin n) : (raised F v i a l).1 = (v l).1 + (if l = i then 1 else 0) := by
    by_cases h : l=i <;> simp [raised,Function.update,h]
  simp [split,Finset.sum_add_distrib]

private lemma smooth_normalized (s : Viewers F) (v : Fin n → S.Tag) {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ ∞ (normalized F s v r) (conf n) :=
  (((S.class_smooth _ (spectate F s).smooth v).comp
     (show ContDiff ℝ ∞ (fun x : Points n => r • x) by fun_prop).contDiffOn
     (fun _ h => Work.A05.smul_conf hr h))).const_smul _

private lemma normalized_gradient (s : Viewers F) (v : Fin n → S.Tag) {r : ℝ} (hr : 0 < r)
    (i : Fin n) (a : Axis) {x : Points n} (hx : x ∈ conf n) :
    Points.gradient i a (normalized F s v r) x = normalized F s (raised F v i a) r x := by
  let f := fun z => S.useAt (spectator F s) z v
  have hy := Work.A05.smul_conf hr hx
  have hf : DifferentiableAt ℝ f (r • x) :=
    (((S.class_smooth _ (spectate F s).smooth v) _ hy).contDiffAt
      ((conf_open _).mem_nhds hy)).differentiableAt (by simp)
  have hz : DifferentiableAt ℝ (fun z => f (r • z)) x :=
    hf.comp x (show DifferentiableAt ℝ (fun z : Points n => r • z) x by fun_prop)
  have hder := F.sector.derivatives.derivative_slot (spectate_evolution F s)
    (spectate F s).laws.toSymmetric (spectate F s).smooth hy i v (v i).2 a
  rw [show update v i (⟨(v i).1,(v i).2⟩ : S.Tag) = v from update_eq_self ..] at hder
  calc
    _ = r ^ (∑ l, (v l).1) • Points.gradient i a (fun z => f (r • z)) x := by
      change fderiv ℝ ((r ^ (∑ l, (v l).1)) • (fun z => f (r • z))) x _ = _
      rw [fderiv_const_smul hz]
      rfl
    _ = _ := by
      rw [Work.A04.gradient_scaled _ _ _ hf]
      rw [← hder, smul_smul, ← pow_succ, normalized, raised_weight]
      rfl

/-- Phase independence for all rescaled position derivatives of fixed fields.
The viewers may vary along the very same sequence. -/
theorem phase_jets (H : Services C f S) (v : Fin n → S.Tag) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hlim : Tendsto r atTop (𝓝 0)) (j : ℕ)
    {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s t : Viewers F,
      ‖iteratedFDeriv ℝ j (normalized F s v (r k) - normalized F t v (r k)) x‖ ≤ ε := by
  induction j generalizing ε v with
  | zero =>
    have h₀ := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hlim (Eventually.of_forall hr)
    have hp := h₀.eventually (phase_bound F H (fun i => (v i).1) (fun i => (v i).2) hK hc (δ := 1/2) (by norm_num))
    have hs : Tendsto (fun k => r k ^ (1 - 1/2 : ℝ)) atTop (𝓝 ((0:ℝ) ^ (1 - 1/2 : ℝ))) :=
      (Real.continuousAt_rpow_const 0 (1 - 1/2 : ℝ) (Or.inr (by norm_num))).tendsto.comp hlim
    rw [Real.zero_rpow (by norm_num : (1 - 1/2 : ℝ) ≠ 0)] at hs
    have hsmall : Tendsto (fun k => 2 * r k ^ (1 - 1/2 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hs.const_mul (2:ℝ)
    filter_upwards [hp,hsmall.eventually_lt_const he] with k hk hm x hx s t
    rw [norm_iteratedFDeriv_zero,Pi.sub_apply,normalized,normalized,← smul_sub]
    exact (hk x hx s t).trans hm.le
  | succ j ih =>
    let D := Fin n × Axis
    let δ := ε / ((Fintype.card D : ℝ)+1)
    have hd : 0 < δ := by unfold δ; positivity
    filter_upwards [eventually_all.mpr (fun b : D => ih (raised F v b.1 b.2) hd)] with k hk x hx s t
    let f := normalized F s v (r k) - normalized F t v (r k)
    have smooth (s : Viewers F) {z : Points n} (hz : z ∈ conf n) :
        ContDiffAt ℝ ∞ (normalized F s v (r k)) z :=
      ((smooth_normalized F s v (hr k)) _ hz).contDiffAt ((conf_open _).mem_nhds hz)
    have hf : ContDiffAt ℝ (↑(j+1 : ℕ)) f x :=
      ((smooth s (hc hx)).sub (smooth t (hc hx))).of_le (WithTop.coe_le_coe.mpr le_top)
    have hdir (b : D) : fderiv ℝ (iteratedFDeriv ℝ j f) x (Points.direction b.1 b.2) =
        iteratedFDeriv ℝ j (normalized F s (raised F v b.1 b.2) (r k) -
          normalized F t (raised F v b.1 b.2) (r k)) x := by
      have hg : Analysis.D (Points.direction b.1 b.2) f =ᶠ[𝓝 x]
          normalized F s (raised F v b.1 b.2) (r k) - normalized F t (raised F v b.1 b.2) (r k) := by
        filter_upwards [(conf_open _).mem_nhds (hc hx)] with z hz
        change fderiv ℝ (_ - _) z _ = _
        rw [fderiv_sub ((smooth s hz).differentiableAt (by simp)) ((smooth t hz).differentiableAt (by simp))]
        exact congrArg₂ (· - ·) (normalized_gradient F s v (hr k) b.1 b.2 hz)
          (normalized_gradient F t v (hr k) b.1 b.2 hz)
      ext u
      calc
        _ = iteratedFDeriv ℝ (j+1) f x (Fin.cons (Points.direction b.1 b.2) u) := by
          rw [iteratedFDeriv_succ_apply_left,Fin.cons_zero,Fin.tail_cons]
        _ = _ := (Analysis.cons_inner hf _ _).trans (by rw [(hg.iteratedFDeriv ℝ j).eq_of_nhds])
    change ‖iteratedFDeriv ℝ (j+1) f x‖ ≤ ε
    rw [← norm_fderiv_iteratedFDeriv]
    apply (Work.B10.norm_le_direction_sum _).trans
    calc
      _ ≤ ∑ _b : D, δ := Finset.sum_le_sum (fun b _ => (congrArg norm (hdir b)).le.trans (hk b x hx s t))
      _ ≤ ε := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right (by linarith : (Fintype.card D : ℝ) ≤ Fintype.card D + 1) hd.le).trans_eq
          (by dsimp [δ]; field_simp)


/-- One prescribed physical insertion surrounded by the release's calibrated probes. -/
def mixedRow (X : Scaling S) (d : ℕ) (e : Exterior (standard C.labels)) (k : ℕ) (a : S.Field d) : ℂ :=
  disc (Fin.cons (α := fun _ : Fin (e.n+1) => S.Tag) ⟨d,a⟩
    (X.pins k ∘ ((freeTable C.labels).classTokens ∘ e.letter))) (X.r k • e.point)

private lemma mixed_point {X : Scaling S} (hX : Pert.FirstExtension F X) {m : ℕ}
    (q : Fin m → (freeTable C.labels).Tag) (b : Fin m → Bool) (ab : Fin m → Axis × Axis)
    {x : Points m} (hx : x ∈ conf m) :
    Tendsto (fun k => disc (Pert.scaledPhysical X F.sector.energy k q b ab) (X.r k • x))
      atTop (𝓝 (disc (Pert.freeWithStress C.labels q b ab) x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := hX.jets m 0 q b ab isCompact_singleton (singleton_subset_iff.mpr hx) (half_pos hε)
  filter_upwards [h] with k hk
  have hh := hk x (mem_singleton _)
  rw [dist_eq_norm]
  simp only [iteratedFDeriv_zero_eq_comp,comp_apply,← map_sub,LinearIsometryEquiv.norm_map] at hh
  exact hh.trans_lt (half_lt_self hε)

open Work.A04 in
/-- A finite family, selected using the free theory alone, determines a column.
Its required measurements involve only leading scalar limits. -/
theorem finite_readings (d : ℕ) : ∃ D : Finset (Exterior (standard C.labels)),
    Injective (LinearMap.pi (fun e : D => row (freeTable C.labels) d e.val)) ∧
    ∀ {X : Scaling S}, Pert.FirstExtension F X → ∀ (a : ℕ → S.Field d) (v : (freeTable C.labels).Field d),
    (∀ e ∈ D, Tendsto (fun k => mixedRow X d e k (a k)) atTop (𝓝 (row (freeTable C.labels) d e v))) →
    Tendsto (fun k => (X.U k d).symm (a k)) atTop (𝓝 v) := by
  classical
  obtain ⟨D,hD⟩ := finite_faithful _ (row_faithful (freeTable C.labels) d)
  refine ⟨D,hD,fun {X} hX a v readings => ?_⟩
  apply tendsto_of_fitted (fun k => LinearMap.pi (fun e : D => approxRow X d e.val k)) _ hD
  · intro p
    apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun k => approxRow X d e.val k p) atTop (𝓝 (row (freeTable C.labels) d e.val p))
    simp_rw [approxRow_eq,row_eq (table_sym _)]
    exact mixed_point F hX (Work.A04.tags _ e.val p) (fun _ => false) (fun _ => (0,0)) e.val.clear
  · apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun k => approxRow X d e.val k ((X.U k d).symm (a k))) atTop (𝓝 (row (freeTable C.labels) d e.val v))
    have eqn (k : ℕ) : approxRow X d e.val k ((X.U k d).symm (a k)) = mixedRow X d e.val k (a k) := by
      rw [approxRow_eq]
      unfold Work.A04.tags mixedRow
      rw [Fin.comp_cons]
      simp only [Scaling.pins,LinearEquiv.apply_symm_apply]
    simpa only [eqn] using readings e.val e.property

open Work.A04 in
/-- In particular the weaker alignment estimate itself holds for the fixed Ward stress. -/
theorem stress_alignment {X : Scaling S} (hX : Pert.FirstExtension F X) (a b : Axis) :
    Tendsto (fun k => (X.U k 4).symm (((X.r k ^ 4 : ℝ) : ℂ) • F.sector.energy a b)) atTop
      (𝓝 (Pert.freeStress C.labels a b)) := by
  obtain ⟨D,_,detect⟩ := finite_readings F 4
  apply detect hX
  intro e _
  let q := Work.A04.tags (freeTable C.labels) e (Pert.freeStress C.labels a b)
  let head := Fin.cons (α := fun _ : Fin (e.n+1) => Bool) true (fun _ => false)
  have h := mixed_point F hX q head (fun _ => (a,b)) e.clear
  have physical (k : ℕ) : Pert.scaledPhysical X F.sector.energy k q head (fun _ => (a,b)) =
      Fin.cons (α := fun _ : Fin (e.n+1) => S.Tag) ⟨4,((X.r k ^ 4 : ℝ) : ℂ) • F.sector.energy a b⟩
        (X.pins k ∘ ((freeTable C.labels).classTokens ∘ e.letter)) := by
    ext1 i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pert.scaledPhysical,head]
    · simp only [Pert.scaledPhysical,head,Fin.cons_succ,Bool.false_eq_true,↓reduceIte]
      change X.pins k (q j.succ) = _
      rw [show q j.succ = (freeTable C.labels).classTokens (e.letter j) from Fin.cons_succ ..]
      rfl
  have free : Pert.freeWithStress C.labels q head (fun _ => (a,b)) = q := by
    ext1 i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Pert.freeWithStress,q,Work.A04.tags,head]
  simp_rw [physical,free] at h
  rw [row_eq (table_sym _)]
  exact h

/-- Column alignment propagates through each physical derivative, keeping the
same fixed insertion, scale sequence, and Maxwell normalization. -/
theorem derivative_alignment {X : Scaling S} (hX : Pert.FirstExtension F X) {d : ℕ} (j : Axis)
    (a : S.Field d) (v : (freeTable C.labels).Field d)
    (h : Tendsto (fun k => (X.U k d).symm (((X.r k ^ d : ℝ) : ℂ) • a)) atTop (𝓝 v)) :
    Tendsto (fun k => (X.U k (d+1)).symm (((X.r k ^ (d+1) : ℝ) : ℂ) • F.sector.derivatives.deriv d j a))
      atTop (𝓝 ((Free.scheme C.labels).deriv d j v)) := by
  have hD := (tendsto_pi_nhds.mp (hX.derivatives d)) j
  have applied := Dash.arcing hD h
  apply applied.congr
  intro k
  apply (X.U k (d+1)).injective
  change X.U k (d+1) (X.r k • (X.carry k (leaves F.sector.derivatives.deriv d j) _)) = _
  rw [← Complex.coe_smul,map_smul,X.carries_f,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change (X.r k : ℂ) • (F.sector.derivatives.deriv d j) (((X.r k ^ d : ℝ) : ℂ) • a) = _
  rw [(F.sector.derivatives.deriv d j).map_smul,smul_smul,pow_succ,Complex.ofReal_mul,mul_comm]


open Next.UVStress in
/-- Convergence of each inserted column in the released Maxwell coordinates
suffices for any sequence of phases and any prescribed columns. -/
theorem aligned_views {X : Scaling S} (hX : Pert.FirstExtension F X)
    (simple : G.Simple) (Q : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (foundation : OPE.Orbits.Foundation F Q) (trace : Trace.Target.Result.{0} F simple)
    (s : ℕ → Viewers F) (d : Fin n → ℕ)
    (u : ℕ → (i : Fin n) → S.Field (d i)) (v : (i : Fin n) → (freeTable C.labels).Field (d i))
    (align : ∀ i, Tendsto (fun k => (X.U k (d i)).symm (u k i)) atTop (𝓝 (v i)))
    {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖S.classMoment (spectator F (s k)) d (X.r k • x) (u k) - (freeTable C.labels).classMoment (freeTable C.labels) d x v‖ ≤ ε := by
  classical
  let E (i : Fin n) := (freeTable C.labels).Field (d i)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let M (k : ℕ) (p : (i : Fin n) → E i) : C(K,ℂ) :=
    ⟨fun x => S.classMoment (spectator F (s k)) d (X.r k • x.val) (fun i => X.U k (d i) (p i)),
      ((S.class_smooth _ (spectate F (s k)).smooth (fun i => ⟨d i,X.U k (d i) (p i)⟩)).continuousOn.comp
        ((show Continuous (fun x : Points n => X.r k • x) by fun_prop).continuousOn)
        (fun _ hx => Work.A05.smul_conf (X.positive k) (hc hx))).restrict⟩
  let W (p : (i : Fin n) → E i) : C(K,ℂ) :=
    ⟨fun x => (freeTable C.labels).classMoment (freeTable C.labels) d x.val p,
      (((freeTable C.labels).class_smooth _ (table_smooth _) (fun i => ⟨d i,p i⟩)).continuousOn.mono hc).restrict⟩
  have basis_limit (p : (i : Fin n) → E i) : Tendsto (fun k => M k p) atTop (𝓝 (W p)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hm := YM.Existence.SelectedJets.ofTrace F X hX simple Q foundation trace
      (fun i => ⟨d i,p i⟩) (fun _ => false) (fun _ => (0,0)) 0 hK hc (half_pos hη)
    filter_upwards [hm] with k hk
    rw [dist_eq_norm]
    apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hη).le).mpr (fun x => ?_)) (half_lt_self hη)
    have h := hk x.val x.property (s k)
    simp only [iteratedFDeriv_zero_eq_comp, comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] at h
    exact h
  let z (k : ℕ) (i : Fin n) : E i := (X.U k (d i)).symm (u k i)
  have expandM (k : ℕ) (p : (i : Fin n) → E i) :
      M k p = ∑ b : Code E, coords E b p • M k (combination E b) := by
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    exact (basis_tuple E p ((S.classMoment (spectator F (s k)) d (X.r k • x.val)).compLinearMap (fun i => (X.U k (d i)).toLinearMap)))
  have expandW (p : (i : Fin n) → E i) :
      W p = ∑ b : Code E, coords E b p • W (combination E b) := by
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    exact (basis_tuple E p ((freeTable C.labels).classMoment (freeTable C.labels) d x.val))
  have hconv : Tendsto (fun k => M k (z k)) atTop (𝓝 (W v)) := by
    rw [show (fun k => M k (z k)) = (fun k => ∑ b : Code E, coords E b (z k) • M k (combination E b)) from
      funext (fun k => expandM k (z k)),expandW v]
    exact tendsto_finsetSum _ (fun b _ => (tendsto_coords E b align).smul (basis_limit (combination E b)))
  filter_upwards [Metric.tendsto_nhds.mp hconv ε he] with k hk x hx
  rw [dist_eq_norm] at hk
  have h := (ContinuousMap.norm_coe_le_norm (M k (z k) - W v) ⟨x,hx⟩).trans hk.le
  change ‖S.classMoment (spectator F (s k)) d (X.r k • x) (fun i => X.U k _ ((X.U k _).symm (u k i))) -
    (freeTable C.labels).classMoment (freeTable C.labels) d x v‖ ≤ ε at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end YM.FixedFieldMaxwell
