import YM.WilsonMS.Stencil.SegmentJet
import YM.WilsonMS.Stencil.Midpoint
/-!
# Link expansion in radial gauge

Use the entire gauge-transformed path. Only need the covariant derivatives
near (0,0); can arrange common neighborhood for each fixed unit edge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.RGerm
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source Paths Lattice RG Wilson
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {B : Paths.Family G} {n : ℕ} (e : Edge Cover)
local notation "I" => unitInterval
local notation "R" => Gauge.Mat G

abbrev alongFrom :=
  Webs.Midpt.station

def travelV (z : ℝ × ℝ) : Domain :=
  (z.1, z.1 • alongFrom e z.2)

def drift (D : Paths.Family G) (z : ℝ × ℝ) :=
  z.1 • D e.2 (travelV e z)

variable {e} in
lemma motion_smooth : ContDiff ℝ ∞ (travelV e) := by
  unfold travelV alongFrom Webs.Midpt.station
  fun_prop

lemma coefficients (h : Flow B) (s : I) : ContDiffAt ℝ (↑n) (drift e (pull B)) (0, (s : ℝ)) := by
  unfold drift
  apply ContDiffAt.smul (f := Prod.fst)
  · exact contDiffAt_fst
  exact
    ContDiffAt.comp (n := ↑n) (g := pull B e.2) (f := travelV e) ((0 : ℝ), s.val)
      (by
        unfold travelV
        simp only [zero_smul]
        exact contDiffAt_infty.mp (pull_s h _) _)
      (contDiffAt_infty.mp motion_smooth.contDiffAt _)

lemma zone (h : Flow B) :
    ∀ᶠ a : ℝ in 𝓝 0, ∀ s : I, DifferentiableAt ℝ (reprQ B) (travelV e (a, s.val)) := by
  let W := {z : Domain | ContDiffAt ℝ (↑(1 : ℕ)) (reprQ B) z}
  let U := (travelV e) ⁻¹' W
  have ht : IsOpen U :=
    IsOpen.preimage motion_smooth.continuous
      (isOpen_iff_mem_nhds.mpr
        (fun y hy =>
          (ContDiffAt.eventually (show ContDiffAt ℝ (↑(1 : ℕ)) (reprQ B) y from hy) (by simp))))
  have hb : ({0} ×ˢ I) ⊆ U := by
    rintro ⟨x, y⟩ ⟨hx, _⟩
    obtain rfl : x = 0 := hx
    change ContDiffAt ℝ (↑(1 : ℕ)) (reprQ B) (travelV e (0, y))
    unfold travelV
    simp only [zero_smul]
    exact (repr_smooth h).of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨u, v, hu, _, hU, hv, H⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) isCompact_Icc ht hb
  filter_upwards [hu.mem_nhds (hU (mem_singleton _))] with x hx j
  exact (show ContDiffAt ℝ (↑(1 : ℕ)) _ _ from H ⟨hx, hv j.property⟩).differentiableAt (by norm_num)

lemma shift (h : Flow B) (a : ℝ) : ContDiff ℝ 1 (fun i => drift e B (a, i)) := by
  unfold drift
  refine ContDiff.const_smul _ ?_
  exact
    ((h _).of_le (by simp)).comp (f := fun i => travelV e (a, i))
      (((show ContDiff ℝ ∞ (travelV e) from motion_smooth).comp (by fun_prop)).of_le (by simp))

def chainU (B : Paths.Family G) (a : ℝ) :=
  track (G := G) (fun i => drift e B (a, i))

def changedU (B : Paths.Family G) (a x : ℝ) : G.El :=
  radialG B (travelV e (a, 0)) * chainU e B a x * (radialG B (travelV e (a, x)))⁻¹

lemma changed_heat (h : Flow B) (a y : ℝ) (ht : DifferentiableAt ℝ (reprQ B) (travelV e (a, y))) :
    HasDerivAt (G.mat ∘ changedU e B a)
      (G.mat (changedU e B a y) * G.colorMat (drift e (pull B) (a, y))) y := by
  let X (x : ℝ) := travelV e (a, x)
  have hx : HasDerivAt X (a • d e.2) y := by
    have hv : HasDerivAt (fun x : ℝ => X x |>.2) (a • basis e.2) y := by
      have he : HasDerivAt (fun i => alongFrom e i) (basis e.2) y := by
        simpa only [alongFrom, Webs.Midpt.station, one_smul] using!
          (((hasDerivAt_id' y).smul_const (basis e.2)).const_add (Work.G03.castPos e.1))
      exact HasDerivAt.const_smul a he
    simpa only [d, Prod.smul_mk, smul_zero] using! (hasDerivAt_const y (X y |>.1)).prodMk hv
  let U := chainU e B a
  let V (x) := G.mat (U x)
  let Q := reprQ B ∘ X
  let R' := fderiv ℝ (reprQ B) (X y) (d e.2)
  let p := reprA B e.2 (X y)
  have ht' : HasDerivAt Q (a • R') y := by
    rw [show a • R' = fderiv ℝ (reprQ B) (X y) (a • d e.2) from Eq.symm (map_smul ..)]
    exact ht.hasFDerivAt.comp_hasDerivAt y hx
  have hw : HasDerivAt V (V y * (a • p)) y := by
    rw [show a • p = G.colorMat (drift e B (a, y)) from Eq.symm (map_smul ..)]
    exact (tracks (shift e h a)).2 _
  let b := Q y
  let c := Q 0
  have hu (x : ℝ) : Q x * star (Q x) = 1 := G.mat_mul_star _
  have hs : HasDerivAt (fun t => star (Q t)) (-star b * (a • R') * star b) y := by
    have he := ht'.star
    have hg : (a • R') * star b + b * star (a • R') = 0 :=
      ((ht'.mul he).unique
        (show HasDerivAt (Q * star Q) 0 y from
          by
          rw [show Q * star Q = (fun _ => 1) from funext hu]
          exact hasDerivAt_const ..))
    refine he.congr_deriv ?_
    have hh := congr_arg (star b * ·) hg
    rw [mul_add, ← mul_assoc (star b) b, show star b * b = 1 from G.mat_star_mul _, one_mul, mul_zero,
      add_comm] at hh
    rw [neg_mul, neg_mul, mul_assoc]
    exact eq_neg_of_add_eq_zero_left hh
  have he : G.colorMat (drift e (pull B) (a, y)) = a • (b * p * star b - R' * star b) := by
    change G.colorMat (a • pull B e.2 _) = _
    rw [map_smul]
    exact congr_arg (a • ·) (formula ht _)
  rw [he]
  have hi (x) : G.mat (changedU e B a x) = c * (V x) * star (Q x) := by
    unfold changedU
    rw [G.mat_mul, G.mat_mul, G.mat_inv]
    rfl
  rw [hi, show G.mat ∘ changedU e B a = (fun x : ℝ => c * V x * star (Q x)) from funext hi]
  apply HasDerivAt.congr_deriv (HasDerivAt.mul (hw.const_mul c) hs)
  change c * (V y * _) * star b + _ * (-star b * _ * star b) = _
  have hb : star b * b = 1 := G.mat_star_mul _
  change _ = c * V y * star b * _
  rw [smul_sub, mul_sub, ← smul_mul_assoc, ← mul_smul_comm, mul_assoc (c * V y), mul_assoc b, ←
    mul_assoc (star b), hb]
  simp only [one_mul, ← smul_mul_assoc, neg_mul, mul_neg]
  simp [mul_assoc, sub_eq_add_neg]

lemma cover_input (t s : ℝ) : (travelV e (t, s)).2 = bridge e.2 (t, (travelV e (t, 1 / 2)).2) s := by
  unfold travelV alongFrom Webs.Midpt.station bridge
  simp only
  module

lemma from_mid (B : Paths.Family G) (t : ℝ) :
    chainU e B t 1 = endLink B e.2 (t, (travelV e (t, 1 / 2)).2) := by
  unfold endLink chainU
  congr 2
  funext s
  unfold heat drift
  congr 3
  exact Prod.ext rfl (cover_input e _ _)

private lemma lead (h : Flow B) :
    ∀ᶠ a : ℝ in 𝓝 0,
      Follow (TPath.injection G) (G.mat ∘ changedU e B a) (along I (drift e (pull B)) a) := by
  filter_upwards [remain_on (fun s (hs : s ∈ I) => coefficients (n := 1) e h ⟨s, hs⟩), zone e h] with
    a ha hv
  refine ⟨?_, fun s => ?_⟩
  · unfold Function.comp changedU
    rw [show chainU e B a 0 = 1 from (tracks (shift e h a)).1, mul_one, mul_inv_cancel, G.mat_one]
  rw [ha]
  exact changed_heat e h a _ (hv s)

def reduced (h : Flow B) (n : ℕ) (z : ℝ × ℝ) :=
  partConnection n (records h z.1) z.1 e z.2

lemma fare (h : Flow B) (v : I) : ContDiffAt ℝ (↑n) (reduced e h n) (0, v.val) := by
  have he (x : ℝ × ℝ) : reduced e h n x = x.1 • potential n (records h x.1) e.2 (travelV e x).2 := rfl
  rw [funext he]
  exact
    ContDiffAt.smul (f := Prod.fst) contDiffAt_fst
      (contDiffAt_infty.mp (((potential_s (k := n) h e.2).comp motion_smooth).contDiffAt) _)

lemma sequence (h : Flow B) : Agree n 0 (along I (drift e (pull B))) (along I (reduced e h n)) := by
  refine
    agree_path (fun v hv => coefficients e h ⟨v, hv⟩) (fun v hv => fare e h ⟨v, hv⟩) fun z hz => ?_
  have ht : ContDiffAt ℝ (↑n) (fun t : ℝ => drift e (pull B) (t, z)) 0 :=
    (coefficients (n := n) e h ⟨z, hz⟩).comp (f := fun t : ℝ => (t, z)) _ (by fun_prop)
  have hu : ContDiffAt ℝ (↑n) (fun t : ℝ => reduced e h n (t, z)) 0 :=
    (fare (n := n) e h ⟨z, hz⟩).comp (f := fun t : ℝ => (t, z)) _ (by fun_prop)
  cases n with
  | zero =>
    refine ⟨ht, hu, ?_⟩
    intro k hk
    obtain rfl := Nat.eq_zero_of_le_zero hk
    apply ContinuousMultilinearMap.ext
    intro x
    simp [drift, reduced, partConnection]
  | succ k =>
    let U (t : ℝ) := travelV e (t, z)
    let V (x : Domain) := potential (k + 1) (records h x.1) e.2 x.2
    let P := pull B e.2
    have hp : ContDiff ℝ ∞ V := potential_s h _
    have hz' : U 0 = (0, 0) := by
      unfold U travelV
      simp only [zero_smul]
    have hs : ContDiffAt ℝ ∞ U 0 :=
      motion_smooth.contDiffAt.comp (f := fun t : ℝ => (t, z)) _ (by fun_prop)
    have hh :
      Agree (k + 1) 0 (fun t : ℝ => t ^ (1 : ℕ) • P (U t)) (fun t : ℝ => t ^ (1 : ℕ) • V (U t)) :=
      power_agree (u := P ∘ U) (v := V ∘ U)
        (contDiffAt_infty.mp
          (ContDiffAt.comp _
            (by
              rw [hz']
              exact pull_s h _)
            hs)
          _)
        (contDiffAt_infty.mp (hp.contDiffAt.comp _ hs) _)
        ((Agree.refl (contDiffAt_infty.mp hs k)).comp
          (by
            rw [hz']
            exact precision h e.2 0))
        (by omega)
    simp_rw [pow_one] at hh
    exact hh

lemma profileH (h : Flow B) (H : Hol G) :
    Agree n 0 (fun t => G.mat (changedU e B t 1))
      (fun t : ℝ => G.mat (H.links n (records h t) t e)) := by
  let f := reduced e h n
  let x := along I f
  let g := drift e (pull B)
  let y := along I g
  have hc := sequence (n := n) e h
  have hb (v) : f (0, v) = 0 := zero_smul ..
  have hv : x 0 = 0 :=
    ContinuousMap.ext fun t => (path_val (p := (0 : ℝ)) (fun s hs => fare e h ⟨s, hs⟩) t).trans (hb _)
  have ht :=
    hc.apply_smooth (u := TPath.step (injection G))
      (by
        rw [show along I (reduced e h n) 0 = 0 from hv]
        exact (analyt_step _).of_le le_top)
  have hy : (fun t : ℝ => G.mat (changedU e B t 1)) =ᶠ[𝓝 0] TPath.step (injection G) ∘ y :=
    reaches (p := (0 : ℝ)) (fun v hv => coefficients (n := n) e h ⟨v, hv⟩) (fun i _ => zero_smul ..) _
      (lead e h)
  let U (t : ℝ) (s : ℝ) := G.mat (H.flow n (records h t) t e s)
  refine
    ((Agree.of_event hy.symm ht.smooth).symm.trans ht).trans
      (Agree.of_event (f := TPath.step (injection G) ∘ x) (g := fun t => U t 1) ?_ ht.smooth')
  apply Filter.EventuallyEq.symm
  apply reaches (p := (0 : ℝ)) (fun v hv => fare e h ⟨v, hv⟩) (fun i _ => hb i) U
  filter_upwards [Curves.remain_on (fun v hv => fare (n := n) e h ⟨v, hv⟩)] with t ht
  refine
    ⟨by
      unfold U
      rw [(H.solves ..).1, G.mat_one], fun v => ?_⟩
  rw [ht]
  exact (H.solves ..).2 _
end YM.WilsonMS.RGerm
