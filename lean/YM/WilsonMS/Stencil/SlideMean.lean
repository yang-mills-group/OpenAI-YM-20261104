import YM.WilsonMS.Stencil.MidHolonomy
/-!
# Triangular inverse of link averaging, all orders in the link logs.

Not approximating the path by its abelianized endpoint. The corrected
smooth potentials are auxiliary to proving admissibility of the SAME
stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Paths
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
local notation "I" => unitInterval
local notation "C" => Gauge.Color G
variable {A K : Axis → E4 → G.Color} {B : Family G} {k n : ℕ} {m : Axis} {t : ℝ} {y : E4}

def addHeat (B : Family G) (K : Axis → E4 → G.Color) (k : ℕ) : Family G := fun i x =>
  B i x + x.1 ^ k • K i x.2

lemma addFlow (h : Flow B) (hh : ∀ i, ContDiff ℝ ∞ (K i)) : Flow (addHeat B K k) := fun i =>
  (h i).add ((contDiff_fst.pow k).smul ((hh i).comp contDiff_snd))

lemma addLine (t s : ℝ) :
    oneHeat (addHeat B K k) m y (t, s) =
      oneHeat B m y (t, s) + t ^ (k + 1) • K m (bridge m (t, y) s) := by
  unfold oneHeat heat addHeat
  simp only [smul_add, pow_succ', mul_smul]

lemma condition_top (h : Flow B) (hh : ∀ i, ContDiff ℝ ∞ (K i)) (e : n ≤ k + 1) (m : Axis) (y : E4) :
    iteratedDeriv n (TraceH (addHeat B K k) m y) 0 - iteratedDeriv n (TraceH B m y) 0 =
      if n = k + 1 then (n.factorial : ℝ) • ContinuousMap.const I (K m y) else 0 := by
  let P := TraceH B m y
  let P' := TraceH (addHeat B K k) m y
  ext1 v
  have he (B : Family G) (h : Flow B) :
    iteratedDeriv n (TraceH B m y) 0 v = iteratedDeriv n (fun t : ℝ => oneHeat B m y (t, v.val)) 0 :=
    path_jet (k := n) (S := I) (fun i hi => traceH_pt h ⟨i, hi⟩) v 1
  change iteratedDeriv n P' 0 v - iteratedDeriv n P 0 v = _
  rw [show iteratedDeriv n P' 0 v = _ from he _ (addFlow h hh),
    show iteratedDeriv n P 0 v = _ from he _ h]
  let Q (t : ℝ) := oneHeat B m y (t, v.val)
  let F (t : ℝ) := K m (bridge m (t, y) v.val)
  have hF : ContDiffAt ℝ (↑n) F 0 :=
    ((hh m).contDiffAt.of_le (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).comp (f :=
      fun t => bridge m (t, y) v.val) _
      (by
        unfold bridge
        fun_prop)
  have hQ : ContDiffAt ℝ (↑n) Q 0 :=
    (traceH_pt (k := n) h v).comp (f := fun t : ℝ => (t, v.val)) _ (by fun_prop)
  rw [show
      (fun t : ℝ => oneHeat (addHeat B K k) m y (t, v.val)) = Q + (fun t : ℝ => t ^ (k + 1) • F t)
      from funext fun t => addLine ..,
    iteratedDeriv_add (g := fun t => t ^ (k + 1) • F t) hQ ((contDiffAt_id.pow (k + 1)).smul hF)]
  change iteratedDeriv n Q 0 + _ - iteratedDeriv n Q 0 = _
  rw [add_sub_cancel_left]
  simp_rw [power_bill hF]
  split <;> rename_i hv
  · have H : n = k + 1 := Nat.le_antisymm e hv
    subst n
    simp only [tsub_self, Nat.choose_self, one_smul, iteratedDeriv_zero, if_true, F, bridge,
      zero_smul, add_zero]
    rfl
  rw [if_neg (by omega)]
  rfl

lemma shape_log (h : Flow B) (hh : ∀ i, ContDiff ℝ ∞ (K i)) (m : Axis) (x : E4) :
    Agree k 0 (fun t => logLink B m (t, x)) (fun t => logLink (addHeat B K k) m (t, x)) ∧
      iteratedDeriv (k + 1) (fun t => logLink (addHeat B K k) m (t, x)) 0 -
          iteratedDeriv (k + 1) (fun t => logLink B m (t, x)) 0 =
        ((k + 1).factorial : ℝ) • K m x := by
  let D := addHeat B K k
  have hd : Flow D := addFlow h hh
  let F := TraceH B m x
  let H := TraceH D m x
  have he : Agree k 0 F H :=
    Agree.line (traceH_s h) (traceH_s hd) fun n hn => by
      obtain hc := condition_top (k := k) h hh (le_trans hn (Nat.le_succ k)) m x
      rw [if_neg (by omega)] at hc
      exact (sub_eq_zero.mp hc).symm
  have h0 : F 0 = 0 := zero_U h
  have ht : ContDiffAt ℝ (↑(k + 1 : ℕ)) (logarithm G) (F 0) := by
    rw [h0]
    exact (chartable G).of_le le_top
  have hu := top_motion (u := logarithm G) (z := fun _ => 1) (traceH_s h) (traceH_s hd) ht he
  change
    iteratedDeriv (k + 1) (logarithm G ∘ H) 0 - iteratedDeriv (k + 1) (logarithm G ∘ F) 0 =
      fderiv ℝ _ (F 0) (iteratedDeriv (k + 1) H 0 - iteratedDeriv (k + 1) F 0) at hu
  obtain ha := sampled_log (k := k + 1) (m := m) (y := x) h
  obtain hb := sampled_log (k := k + 1) (m := m) (y := x) hd
  refine
    ⟨(ha.lower (Nat.le_succ _)).trans
        ((he.apply_smooth (he.value ▸ ht.of_le (Nat.cast_le.mpr (Nat.le_succ k)))).trans
          (hb.lower (Nat.le_succ _)).symm),
      ?_⟩
  rw [hb.along_line le_rfl, ha.along_line le_rfl,
    show
      iteratedDeriv (k + 1) (logarithm G ∘ TraceH (addHeat B K k) m x) 0 -
          iteratedDeriv (k + 1) (logarithm G ∘ TraceH B m x) 0 =
        _
      from hu]
  rw [show iteratedDeriv (k + 1) H 0 - iteratedDeriv (k + 1) F 0 = _ from
      condition_top h hh (le_refl (k + 1)) m x,
    if_pos rfl, h0, map_smul, log_const]

lemma port_smooth {U X Y : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : U × X → Y} {x : U} {p : X}
    (h : ContDiffAt ℝ ∞ F (x, p)) (s : Fin k → U) :
    ContDiffAt ℝ ∞ (fun p : X => iteratedFDeriv ℝ k (fun x => F (x, p)) x s) p := by
  have ht :
    (fun p : X => iteratedFDeriv ℝ k (fun x => F (x, p)) x s) =ᶠ[𝓝 p] fun p : X =>
      iteratedFDeriv ℝ k F (x, p) (fun i => (s i, 0)) := by
    have hp : ContDiffAt ℝ (↑k) F (x, p) := h.of_le (WithTop.coe_le_coe.mpr le_top)
    filter_upwards [((continuous_const.prodMk continuous_id).continuousAt (x := p)).tendsto.eventually
        (hp.eventually (by simp))] with
      y hy
    exact (partial_first hy s).symm
  apply ContDiffAt.congr_of_eventuallyEq _ ht
  let L := ContinuousMultilinearMap.apply ℝ (fun _ => U × X) Y (fun i : Fin k => (s i, 0))
  exact
    L.contDiff.contDiffAt.comp (f := fun y : X => iteratedFDeriv ℝ k F (x, y)) p
      ((h.iteratedFDeriv_right (i := k) (m := ∞)
            (by
              change ((↑((⊤ : ℕ∞) + (k : ℕ∞)) : WithTop ℕ∞) ≤ _)
              simp)).comp
        (f := fun y : X => (x, y)) _ (by fun_prop))

lemma flow_matches_succ (h : Flow B) (hA : ∀ i, ContDiff ℝ ∞ (A i)) (hh : Matches A B (k + 1)) :
    ∃ D : Family G, Flow D ∧ (∀ i y, D i (0, y) = B i (0, y)) ∧ Matches A D (k + 2) := by
  let K (i : Axis) (y : E4) :=
    (((k + 2).factorial : ℝ))⁻¹ •
      (iteratedDeriv (k + 2) (fun t : ℝ => feed (A i) (t, y)) 0 -
        iteratedDeriv (k + 2) (fun t => logLink B i (t, y)) 0)
  have hp (i) : ContDiff ℝ ∞ (K i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    apply ContDiffAt.const_smul
    apply ContDiffAt.sub
    · exact
        port_smooth (p := x)
          (show ContDiffAt ℝ ∞ (feed (A i)) (0, x) from
            (contDiff_fst.smul ((hA i).comp contDiff_snd)).contDiffAt)
          (fun _ : Fin _ => 1)
    exact
      port_smooth (p := x)
        ((contDiffAt_infty (f := logLink B i)).mpr fun n => (loglink (k := n) h).smooth)
        (fun _ : Fin _ => 1)
  let D := addHeat B K (k + 1)
  have hd : Flow D := addFlow h hp
  refine
    ⟨D, hd,
      (fun i y => by simp only [D, addHeat, zero_pow (Nat.succ_ne_zero _), zero_smul, add_zero]), ?_⟩
  intro m y
  obtain ⟨ep, ec⟩ := shape_log (k := k + 1) h hp m y
  refine Agree.line (contDiffAt_id.smul (contDiffAt_const (c := A m y))) (sampled_log hd).smooth ?_
  intro n hn
  rcases lt_or_eq_of_le hn with hq | rfl
  · exact ((hh m y).trans ep).along_line (by omega)
  unfold K at ec
  rw [smul_inv_smul₀ (by positivity)] at ec
  exact (sub_left_inj.mp ec).symm

lemma reverse_mean (A : Axis → E4 → G.Color) (hA : ∀ i, ContDiff ℝ ∞ (A i)) (k : ℕ) :
    ∃ B : Family G, Flow B ∧ (∀ i x, B i (0, x) = A i x) ∧ Matches A B (k + 1) := by
  induction k with
  | zero =>
    let B : Family G := fun i x => A i x.2
    have h : Flow B := fun i => (hA i).comp (f := Prod.snd) contDiff_snd
    exact ⟨B, h, fun _ _ => rfl, fun i x => begin_wave h i x⟩
  | succ k ih =>
    obtain ⟨B, h, hx, H⟩ := ih
    obtain ⟨D, hD, hy, hT⟩ := flow_matches_succ h hA H
    exact ⟨D, hD, fun i x => (hy i x).trans (hx i x), hT⟩

lemma realized {k : ℕ} (h : Matches A B k) (ht : Flow B) (hp : ∀ i, ContDiff ℝ ∞ (A i)) :
    Agree k (0, y) (fun x => G.mat (G.lieExp (feed (A m) x))) (fun x => G.mat (endLink B m x)) := by
  have he : Agree k (0, y) (feed (A m)) (logLink B m) :=
    family
      ((contDiff_fst.smul
          ((hp m |>.of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd)).contDiffAt)
      (loglink ht).smooth (Eventually.of_forall fun i n hn => (h m i).same n hn)
  refine
    (he.apply_smooth (u := G.mat ∘ G.lieExp) (G.exp_jet.contDiffAt.of_le le_top)).trans
      (Agree.symm ?_)
  apply Agree.of_event _ (profile ht).smooth
  filter_upwards [in_chart (m := m) (y := y) ht] with x hx
  exact congr_arg G.mat hx.symm
end YM.WilsonMS.Paths
