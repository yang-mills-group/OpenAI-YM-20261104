import YM.WilsonMS.Stencil.DualGrade
/-!
# Reindex the dimensional calculation (including traces in the complement)

On mark rows act by the same signed permutation on rank, the original axes, and the
first four components of momentum. Keep spin of the remaining components free.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.HBeam
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Landau Arts Pilot Spin Momentum Detect Outlook
open scoped Topology ContDiff
variable {G : Gauge} {n m : ℕ} {A C : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

abbrev passed (X Y : Spin A) : Spin A :=
  ⟨X.turn.trans Y.turn, fun x y => by
    change pairing (Y.turn (X.turn x)) (Y.turn (X.turn y)) = _
    rw [Y.rad, X.rad]⟩

lemma beam_trans (X Y : Spin A) (F : Plane.Row (Leg A C) (Momentum A) ℂ) :
    (leggo C X).beam ((leggo C Y).beam F) = (leggo C (passed X Y)).beam F := by
  let W := leggo (A := A) C
  let P := passed X Y
  have he (a b : A) : (P.profile a b : ℂ) = ∑ i : A, (X.profile a i : ℂ) * (Y.profile i b : ℂ) := by
    change ((Y.turn (X.turn (spray a)) b : ℝ) : ℂ) = _
    rw [← Y.orth, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_mul ..
  funext l
  induction l generalizing F with
  | nil => simp
  | cons a l ih =>
    obtain ⟨⟨⟨_ | a, b⟩, c⟩, p⟩ := a
    · rw [fromG, fromG]
      rw [show
          Koszul.D (((none, b), c), _) ((W Y).beam F) = (W Y).beam (Koszul.D (((none, b), c), _) F)
          from ?_,
        ih]
      exact funext (fun w => show (W Y).beam F (_ :: w) = _ from fromG ..)
    let D (i : A) (p : Momentum A) := Koszul.D (R := ℂ) (((some i, b), c), p)
    let q := X.turn p
    let r := Y.turn q
    let f i := D i r F
    have ht i : D i q ((W Y).beam F) = ∑ j : A, (Y.profile i j : ℂ) • (W Y).beam (f j) := by
      funext v
      rw [Finset.sum_apply]
      exact fromV ..
    rw [fromV, fromV]
    change
      ∑ j : A, (X.profile a j : ℂ) * ((W X).beam (D j q ((W Y).beam F)) l) =
        ∑ i : A, (P.profile a i : ℂ) * (W P).beam (f i) l
    simp_rw [ht, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, he,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ i, ((W X).beam ((W Y).beam (f i))) l = (W P).beam (f i) l from fun i => ih (f i),
      mul_assoc]

omit [DecidableEq A] in
lemma spin_ext {X Y : Spin A} (H : ∀ p, X.turn p = Y.turn p) : X = Y := by
  cases X with
  | mk x h =>
    cases Y with
    | mk y ht =>
      obtain he : x = y := ContinuousLinearEquiv.ext (funext H)
      subst y
      rfl

lemma on_sprays {X Y : Spin A} (H : ∀ i, X.turn (spray i) = Y.turn (spray i)) : X = Y := by
  apply spin_ext
  intro p
  rw [← standardP p]
  simp_rw [map_sum, map_smul, H]

variable (s : Signed)
section moves

abbrev grip : Spin (Arts.L n) :=
  arch (Nat.zero_le n) (hand s)

abbrev shiftR (s : Signed) (G : Gauge) (n : ℕ) :=
  (flagS (grip s) G |>.beam : Rack G n →ₗ[ℂ] Rack G n)

def splitA (s : Signed) (n : ℕ) : Arts.L n ≃ Arts.L n :=
  let P := equivS (Nat.zero_le n);
  (P.symm.trans (Equiv.sumCongr s.perm (Equiv.refl (Apart 0 n)))).trans P

def flare (s : Signed) (n : ℕ) (i : Arts.L n) : ℝ :=
  Sum.elim (fun a => if s.flip a then -1 else 1) (fun _ => 1) ((equivS (Nat.zero_le n)).symm i)
local notation "h" => Nat.zero_le n

lemma split_left (p : Axis) : splitA s n (rises h p) = rises h (s.perm p) := by
  simp only [splitA, Equiv.trans_apply, show rises h p = equivS h (Sum.inl p) from rfl,
    Equiv.symm_apply_apply]
  rfl

lemma split_right (p : Apart 0 n) : splitA s n (aside h p) = aside h p := by
  unfold splitA
  simp only [Equiv.trans_apply, show aside h p = equivS h (Sum.inr p) from rfl,
    Equiv.symm_apply_apply]
  rfl

lemma flare_left (i : Axis) : flare s n (rises h i) = (if s.flip i then -1 else 1) := by
  unfold flare
  rw [show rises h i = equivS h (.inl i) from rfl, Equiv.symm_apply_apply]
  rfl

lemma flare_r (i : Apart 0 n) : flare s n (aside h i) = 1 := by
  unfold flare
  rw [show aside h i = equivS h (.inr i) from rfl, Equiv.symm_apply_apply]
  rfl

lemma low (a : Axis) :
    (hand s).turn (spray a) = ((if s.flip a then (-1 : ℝ) else 1)) • spray (s.perm a) := by
  change s.act _ = _
  ext i
  obtain ⟨j, rfl⟩ := s.perm.surjective i
  rw [s.act_at]
  by_cases he : j = a
  · subst j
    simp only [spray, Pi.single_eq_same]
    cases hp : s.flip a <;> simp
  cases hv : s.flip j <;> cases ht : s.flip a <;> simp [he, spray]

lemma sends (i : Arts.L n) : (grip s).turn (spray i) = (flare s n i) • spray (splitA s n i) := by
  rcases rangeA i h with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [grip, split_left, ← send_spray, arch_on, low, map_smul, send_spray, flare_left]
  rw [grip, split_right, flare_r, one_smul, ← send_spray, arch_identity]

lemma tower (hx : m ≤ n) : arch hx (grip s) = grip s := by
  refine on_sprays fun i => ?_
  rcases rangeA i hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [← send_spray, arch_on]
    rw [sends, map_smul, send_spray, send_spray, sends]
    rcases rangeA i (Nat.zero_le m) with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [show rises hx (rises (Nat.zero_le m) i) = rises h i from rfl, split_left, flare_left,
        flare_left, split_left]
      rfl
    obtain ⟨j, hj⟩ : ∃ j : Apart 0 n, rises hx (aside (Nat.zero_le m) i) = aside h j := by
      rcases rangeA (rises hx (aside (Nat.zero_le m) i)) h with ⟨p, hp⟩ | ⟨j, hj⟩
      exact (nowhere (Nat.zero_le m) p i ((rises hx).injective hp)).elim
      exact ⟨j, hj.symm⟩
    rw [flare_r, split_right, hj, flare_r, split_right]
  obtain ⟨j, hj⟩ : ∃ j : Apart 0 n, aside hx i = aside h j := by
    rcases rangeA (aside hx i) h with ⟨p, hp⟩ | ⟨j, hj⟩
    exact (nowhere hx (rises (Nat.zero_le m) p) i hp).elim
    exact ⟨_, hj.symm⟩
  rw [← send_spray, arch_identity, send_spray, hj, sends, flare_r, split_right, one_smul]

lemma grip0 : grip (n := 0) s = hand s :=
  on_sprays fun i => by
    let H := Nat.zero_le 0
    rw [show i = rises H i from Fin.ext rfl, sends, flare_left, split_left,
      show rises H i = i from Fin.ext rfl, show rises H (s.perm i) = s.perm i from Fin.ext rfl,
      low s i]

lemma after (u : Signed) : passed (grip s) (grip (n := n) u) = grip (u * s) := by
  apply on_sprays
  intro i
  rcases rangeA i h with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [← send_spray]
    change (grip u).turn ((grip s).turn (Left h _)) = _
    simp only [grip, arch_on]
    congr 1
    exact (Signed.act_mul ..).symm
  change (grip u).turn ((grip s).turn _) = _
  rw [← send_spray]
  simp only [grip, arch_identity]

abbrev cod (s : Signed) (i : Cfield G n) : Cfield G n :=
  ((i.1.1.map (splitA s n), i.1.2), i.2)

abbrev digit (s : Signed) (i : Cfield G n) : ℝ :=
  Option.elim' 1 (flare s n) i.1.1

abbrev mov (s : Signed) (i : Shore G n) : Shore G n :=
  (cod s i.1, (grip s).turn i.2)

abbrev signs (s : Signed) (l : Legs (Shore G n)) : ℂ :=
  (l.map (fun i => (digit s i.1 : ℂ))).prod

lemma phase (F : Rack G n) (l : Legs (Shore G n)) :
    shiftR s G n F l = signs s l * F (l.map (mov s)) := by
  induction l generalizing F with
  | nil => simp [signs]
  | cons i l ih =>
    obtain ⟨⟨⟨_ | a, b⟩, c⟩, p⟩ := i
    · rw [show shiftR s G n = beam (leggo G.ColorIndex (grip s)) from rfl, fromG]
      rw [show ∀ F, beam (leggo G.ColorIndex (grip s)) F l = _ from ih]
      change signs s l * _ = ((1 : ℂ) * signs s l) * _
      rw [one_mul]
      rfl
    change shiftR s G n F ((vleg b a c, p) :: l) = _
    rw [show shiftR s G n _ _ = _ from cols (sends s a) F b c l p,
      show ∀ F, (leggo G.ColorIndex (grip (n := n) s)).beam F l = _ from ih]
    change _ = ((flare s n a : ℂ) * signs s l) * _
    rw [mul_assoc]
    rfl
end moves

def rotateMob (s : Signed) (G : Gauge) : Mob G →ₗ[ℂ] Mob G
    where
  toFun V n := shiftR s G n (V n)
  map_add' V W := funext fun i => map_add (shiftR s G i) (V i) (W i)
  map_smul' x V := funext fun i => map_smul (shiftR s G i) x (V i)

lemma sequence (t : Signed) (F : Mob G) : rotateMob s G (rotateMob t G F) = rotateMob (t * s) G F :=
  funext fun i => by
    change beam (leggo _ _) (beam (leggo _ _) (F i)) = beam (leggo _ (grip (t * s))) _
    rw [beam_trans]
    exact congr_arg (fun p => (flagS p G).beam (F i)) (after s t)

lemma headed (F : Mob G) : rotateMob 1 G F = F := by
  funext n
  let X := grip (n := n) 1
  let m : Signed := 1
  have hx (i : Arts.L n) : X.turn (spray i) = (1 : ℝ) • spray i := by
    rcases rangeA i (Nat.zero_le n) with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [show X.turn _ = _ from sends m _, split_left, flare_left]
      rfl
    rw [show X.turn _ = _ from sends m _, split_right, flare_r]
  have hp (p : SectorP n) : X.turn p = p := by
    rw [← standardP p]
    simp_rw [map_sum, map_smul, hx, one_smul]
  suffices ht : ∀ V : Rack G n, beam (leggo _ X) V = V from ht (F n)
  intro F
  funext l
  induction l generalizing F with
  | nil => simp
  | cons i l ih =>
    obtain ⟨⟨⟨_ | a, b⟩, c⟩, p⟩ := i
    · rw [fromG, ih, hp]
      rfl
    change beam (leggo _ X) F ((vleg b a c, p) :: l) = _
    rw [cols (hx a), ih, hp]
    simp
    rfl

lemma carries {V : Mob G} (H : Sturdy false V) : Sturdy false (rotateMob s G V) := by
  constructor
  · intro n X hx
    let Q := grip (n := n) s
    let P := passed (passed Q.back X) Q
    have ht : P.within false := by
      let h := Nat.zero_le n
      intro hz p
      let r := (hand s).back.turn p
      have hu : Q.turn (Left h r) = Left h p := by
        unfold Q r grip
        rw [arch_on, front]
      change Q.turn (X.turn (Q.back.turn _)) = _
      rw [← hu, rear, hx rfl, hu]
    change beam (leggo _ X) (beam (leggo _ Q) (V n)) = _
    have hm : passed Q P = passed X Q :=
      spin_ext
        (fun p => by
          change Q.turn (X.turn (Q.back.turn (Q.turn _))) = Q.turn (X.turn _)
          rw [rear])
    rw [beam_trans, ← hm, ← beam_trans, show beam (leggo _ P) (V n) = V n from H.turn n _ ht]
    rfl
  intro m n hx i
  change beam (flagS (grip s) G) (V n) _ = _
  rw [← tower s hx, Spin.telescopeS, show (fun x => _) = V m from funext (H.grows hx)]
  rfl
end YM.WilsonMS.HBeam
