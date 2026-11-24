import YM.Trace2.Transfer
import YM.Work.A04
import YM.Work.B10
import YM.Integration.WilsonOneFrameFixedReadings

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOneFrameOriginalPhases
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
theorem original (H : Services C f S) (v : Fin n → S.Tag) {r : ℕ → ℝ}
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



end YM.Integration.WilsonOneFrameOriginalPhases
end
