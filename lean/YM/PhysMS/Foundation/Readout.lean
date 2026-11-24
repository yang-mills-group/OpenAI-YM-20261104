import YM.OPE.Short.Unison
import YM.Work.A05.Window
import YM.Work.B10

/-!
# Removing character dependence for the correlation comparison

For these asymptotic (perturbative) queries it is enough to compare in the **unselected**
hierarchy. This isn't replacing the target all-character quantifier by a.e. or an average: the
**price of the replacement**, uniform over every character and all lengths, is smaller than any
needed coupling power. Use the compatible nonperturbative OPE through the engineering gap *in the
same Final's hierarchy*. This works for arbitrary actual multiple-insertion correlations in a fixed
filtration presentation, and costs the engineering powers before comparing; we also give the
jet estimates so it can be used pointwise without comparing through coordinate-tie problems of
cutoff approximations. For *moving-frame* readings the caller will additionally have to supply
appropriate frame rate control. No assertion about a macroscopic spectator correlator in this file
(i.e. one with some extra slots **not** undergoing the zoom) being character independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS
open Function Filter Set Spec OPE OPE.Orbits OPE.Nesting
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (X : Climb.Scaling S) (h : G.Simple) (H : Foundation F R)
local notation "emptyTags" => (fun z=> Short.extra (S:=S) (z:=z))

section
variable {I : Type} [Fintype I]

def charge (v : I → S.Tag) : ℕ := ∑ i, (v i).1
lemma charge_eq (v : I → S.Tag) : (charge v:ℝ) = weight (degrees v) := by
  unfold charge weight degrees; push_cast; rfl
include X h H
/-- All slots (incl. zero of them), any tags on the actual fields and center, real lengths (not
    special lattice/RG sequences). Rank gap uses X, but nothing follows its radii. Uniform even if we
    select a *different phase for every length and every requested configuration*. Gives also an
    error estimate on the real-split **identity coefficient**, on the common actual Reader. -/
theorem phase_values (v : I → S.Tag) (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (he : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o →
      ∀ q : Viewers F,
        r^charge v * ‖moment (spectator F q) x (voices v) - Short.scalar F R x v o‖ ≤ r^(4-ε) := by
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)),
    H.discrepancy I Empty _ _ (voices v) (voices emptyTags) M η 1 ε hM hη zero_lt_one he 3]
    with r hr hx x o hw q
  obtain ⟨hxy,-,-,hz⟩ := hx x o Short.gapPos hw (by constructor <;> intro z <;> cases z)
  have hd := Short.identity_formula F R X h x v o q (beside_distinct.mp hxy).1
  rw [← hd,Short.Bottom.unchanged F R X h v emptyTags _ 0 (by norm_num)]
  replace hr : 0 < r := hr
  refine (mul_le_mul_of_nonneg_left (hz q) (by positivity)).trans ?_
  apply le_of_eq
  rw [← Real.rpow_natCast, ←Real.rpow_add hr, charge_eq]; congr 1; push_cast; ring
end
variable {n : ℕ}
abbrev Word (S : Table C.book) (n : ℕ) := Fin n → S.Tag

/-- Physical engineering-scaled correlation: a point kernel on conf. Junk on collision. -/
def value (q : Viewers F) (v : Word (C:=C) S n) (r : ℝ) (x : Points n) :=
    (r^charge v) • S.useAt (spectator F q) (r • x) v

lemma conf_room {M η : ℝ} {x : Points n} (hη : 0 < η)
    (hx : WithinRoom 1 M η x.ofLp 0) : x ∈ conf n := Short.plate_conf hη x.ofLp hx

lemma scale_room {M η : ℝ} {x : Points n} {r : ℝ} (hη : 0 < η)
    (hr : 0 < r) (hx : WithinRoom 1 M η x.ofLp 0) : WithinRoom r M η (r • x).ofLp 0 := by
  convert Short.fitted hη hr.le x.ofLp 0 hx using 1
  exact funext fun j=> Eq.trans (by rfl : (r • x).ofLp j=r • x j) (add_zero _).symm

lemma point_moment (q : Viewers F) {x : Points n} (v : Word (C:=C) S n) (hx : x∈conf n) :
    S.useAt (spectator F q) x v=Orbits.moment (spectator F q) x.ofLp (voices v) := by
  rw [Orbits.observed,named_fin _ (spectate F q).laws.toSymmetric _ hx]; rfl

lemma value_tied (q : Viewers F) (v : Word (C:=C) S n) {r : ℝ} {x : Points n}
    (hr : 0 < r) (hx : x∈conf n) :
    ContDiffAt ℝ ∞ (value F q v r) x := by
  have hp := Work.A05.smul_conf hr hx
  exact (((S.class_smooth _ (spectate F q).smooth v).contDiffAt
    ((conf_open _).mem_nhds hp)).comp (f:=fun x=>r • x) x (contDiffAt_id.const_smul r)).const_smul _

-- Retain full order cost by using the derivative plan, same even for the phase views.
-- (No closed-coincidence claim.)
def raised (v : Word (C:=C) S n) (i : Fin n) (a : Axis) : Word (C:=C) S n :=
    update v i ⟨(v i).1+1,F.sector.derivatives.deriv (v i).1 a (v i).2⟩

lemma raised_charge (v : Word (C:=C) S n) (i : Fin n) (a : Axis) :
    charge (raised F v i a) = charge v + 1 := by
  unfold charge raised; change ∑ x, ((Sigma.fst ∘ (update v i (⟨(v i).1+1,F.sector.derivatives.deriv _ a (v i).2⟩ : S.Tag))) x) = (∑ x, (Sigma.fst ∘ v) x) + _
  rw [Function.comp_update]; simp [Finset.sum_update_of_mem]
  rw [← Finset.erase_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  ac_rfl

lemma value_gradient (q : Viewers F) (v : Word (C:=C) S n) {r : ℝ} {x : Points n} (hr : 0 < r)
    (hx : x ∈ conf n) (i : Fin n) (a : Axis) : Analysis.D (Points.direction i a)
      (value F q v r) x = value F q (raised F v i a) r x := by
  let f(x : Points n) := S.useAt (spectator F q) x v
  let g(x : Points n) := f (r • x)
  have hp := Work.A05.smul_conf hr hx
  have hf : DifferentiableAt ℝ f (r • x) :=
    ((S.class_smooth _ (spectate F q).smooth v).contDiffAt ((conf_open _).mem_nhds hp)).differentiableAt (by simp)
  have he := F.sector.derivatives.derivative_slot (spectate_evolution F q)
    (spectate F q).laws.toSymmetric (spectate F q).smooth hp i v (v i).2 a
  rw [show update v i (⟨(v i).1, (v i).2⟩ : S.Tag) = v from update_eq_self ..] at he
  calc
    _ = (r^charge v) • Points.gradient i a g x := by
        unfold Analysis.D; change fderiv ℝ (fun y => (r^charge v) • g y) x _ = _
        have hg : DifferentiableAt ℝ g x := hf.comp x (differentiableAt_id.const_smul r)
        rw [fderiv_fun_const_smul hg]; rfl
    _ = (r^charge (raised F v i a)) • Points.gradient i a f (r • x) := by
        rw [show Points.gradient i a g x=_ from Work.A04.gradient_scaled r f x hf i a,smul_smul,raised_charge,pow_succ]
    _ = _ := congr_arg _ he.symm

include X H h
lemma scalar_read (v : Word (C:=C) S n) {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (he : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : Points n), WithinRoom 1 M η x.ofLp 0 →
      ∀ q : Viewers F, ‖value F q v r x - (r^charge v) • Short.scalar F R (r • x).ofLp v 0‖ ≤ r^(4-ε) := by
  filter_upwards [phase_values F R X h H v M η ε hM hη he,self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with r hL hr x hx q
  replace hr : 0 < r := hr
  rw [value, point_moment F q v (Work.A05.smul_conf hr (conf_room hη hx)), ← smul_sub,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le _)]
  exact hL (r • x).ofLp 0 (scale_room hη hr hx) q

/-- Decouple the phases at any derivative order. Recurrence on these *actual continuum* jets does
    not cost extra relative spacing powers, on the stated normalized coordinates. In particular
    there is not a different period extraction for the derivative estimate. -/
theorem phase_jets (v : Word (C:=C) S n) {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (he : 0 < ε) (j : ℕ) : ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : Points n), WithinRoom 1 M η x.ofLp 0 →
      ∀ (p q : Viewers F),
        ‖iteratedFDeriv ℝ j (value F p v r - value F q v r) x‖ ≤
          (Fintype.card (Fin n × Axis) : ℝ)^j * (2 * r^(4-ε)) := by
  induction j generalizing v with
  | zero =>
    filter_upwards [scalar_read F R X h H v hM hη he] with r hP x hx p q
    rw [norm_iteratedFDeriv_zero, Pi.sub_apply,pow_zero,one_mul,two_mul]
    let A := (r ^ charge v) • Short.scalar F R (r • x).ofLp v 0
    calc
      _ ≤ ‖value F p v r x - A‖ + ‖A - value F q v r x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (hP x hx p) ((norm_sub_rev ..).trans_le (hP x hx q))
  | succ j IH =>
    let v'(b : Fin n × Axis) := raised F v b.1 b.2
    filter_upwards [show ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (b : Fin n × Axis), _ from
      eventually_all.mpr (fun b => IH (v' b)), self_mem_nhdsWithin (s:=Ioi (0:ℝ))]
      with r hB hr x hx p q
    let u := Fin n × Axis
    let f(w : Word (C:=C) S n) := (value F p w r - value F q w r)
    replace hr : 0 < r := hr
    have hσ(w : Word (C:=C) S n) (p : Viewers F) {y} (hy : y∈conf n) : DifferentiableAt ℝ (value F p w r) y :=
        (value_tied F p w hr hy).differentiableAt (by simp)
    rw [← norm_fderiv_iteratedFDeriv]
    refine (Work.B10.norm_le_direction_sum _).trans ((Finset.sum_le_sum ?_).trans (le_of_eq
      (show ∑ _ : u, (Fintype.card (Fin n × Axis) : ℝ)^j*(2*r^(4-ε)) = _ by rw [Finset.sum_const,Finset.card_univ]; dsimp only [u]; ring)))
    intro b _
    let T : Points n := Points.direction b.1 b.2
    have hz := conf_room hη hx
    have hs : Analysis.D T (f v) =ᶠ[𝓝 x] f (v' b) := by
       filter_upwards [(conf_open _).mem_nhds hz] with y hy
       unfold f Analysis.D; rw [fderiv_sub (hσ v p hy) (hσ v q hy)]
       exact congr_arg₂ HSub.hSub (value_gradient F p v hr hy b.1 b.2) (value_gradient F q v hr hy b.1 b.2)
    have hf : ContDiffAt ℝ (↑(j+1 : ℕ)) (f v) x :=
       ((value_tied F p v hr hz).sub (value_tied F q v hr hz)).of_le (WithTop.coe_le_coe.mpr le_top)
    change ‖fderiv ℝ _ x T‖ ≤ _
    have hd : fderiv ℝ (iteratedFDeriv ℝ j (f v)) x T = iteratedFDeriv ℝ j (f (v' b)) x := by
       ext y
       rw [← (show iteratedFDeriv ℝ (j+1) (f v) x (Fin.cons T y) = fderiv ℝ (iteratedFDeriv ℝ j (f v)) x T y from by
               rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons])]
       exact (Analysis.cons_inner hf T y).trans (by rw [(hs.iteratedFDeriv ℝ j).eq_of_nhds])
    exact (congr_arg norm hd).trans_le (hB b x hx p q)
end YM.PhysMS
