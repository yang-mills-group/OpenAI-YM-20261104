import YM.WilsonMS.Calibration.TacticsW
/-!
# Tuning for the generalized stencil menu

Prove `Installed`, the extension of `TaylorOK` to the full bare columns.
Each *subterm* of a column is handled on its own field powers, resulting in
marks compatible with the actual `Circle` condition. Use this to prove
the required high-score matching to the MS archives. Branch not required
symmetric at this stage.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open Wind Wind.Leading Domain
open scoped Topology ContDiff
variable {G : Gauge} {p q : Team} {d k r : ℕ} {u : ℤ}
local notation "B" => Ensure.deck G
variable (W : BasisMenu G)

def rowFull (p : Team) (A : Acts B d) : Dec G :=
  (Wind.member (skyPC G p) (circleScore W p A)).choose

lemma feeds (p : Team) (A : Acts B d) : PM (scoreW W p A) (skyline G p) (rowFull W p A) 0 :=
  (Wind.member (skyPC G p) (circleScore W p A)).choose_spec

lemma rows_same (A C : Acts B d) (h : ∀ i < k, A i = C i) :
    ∀ i < k, rowFull W p A i = rowFull W p C i :=
  mark_birth (feeds W p A) (feeds W p C) fun j hj x =>
    retained W p A j C (fun i hi => h i (by omega)) x

lemma recognition {A C : Acts B d} {Z : ℝ → Law G} (h : Ability W p A C k r u Z) :
    Knick (rowFull W p A k) (rowFull W p C k) r u false Z := by
  let T := rowFull (d := d) W p
  let F' := skyline G p
  have he : Wind.path 1 k 0 F' (T A) = Wind.path 1 k 0 F' (T C) :=
    path_eq _ _ _ (fun _ _ => rfl) (fun i hv => rows_same W A C h.past i (path_in hv).2)
  refine
    knick ((feeds W p A).owes k) ((feeds W p C).owes k) ((feeds W p A).recu k) (fun x => ?_) h.jet
      h.size
  rw [he]
  exact (feeds W p C).recu k x

def seekW (p : Team) (d : ℕ) : Knobs (fun _ => Tact B d) G
    where
  wake A := col (rowFull W p A)
  stay A C i
    h := by
    funext y
    unfold col
    rw [rows_same W A C (k := i + 1) (fun j hj => h j (by omega)) _ (by omega)]

lemma mark_seekW (h : G.Simple) : Marked (seekW W p d) (col (skyline G p)) B d
    where
  law A := PMSolve h (skyPC G p) (feeds W p A) (circleScore W p A) (fun x => properShift W p A h x)
  occurs A := post_ok _ (feeds W p A).owes
  moves A i r v hv ht a b hp hq hk
    hK := by
    obtain ⟨Q, X, H1, H2, H⟩ := room (n := i) W p A hv ht hp hq hk hK
    exact
      ⟨_,
        rewind (K := seekW W p d) (hp := A) (hq := Menus.patch A Q X i) rfl rfl H.past
          (fun x => (((feeds W p A).owes i).stay x).joint)
          (fun x => (((feeds W p _).owes i).stay x).joint) (recognition W H)⟩
variable {P : Acts (Ensure.deck G) d} {j : Glyph (Ensure.deck G) d} {F S : Recount G}

lemma cap0W (p : Team) (h : FitOrder j (P 0)) (x : ℝ) :
    Limit (scoreW W p P x 0).val j.grade ∧ Fits (scoreW W p P x 0) j.read j.grade j.size false := by
  let A0 := scoreW W p P x 0
  let f (c : Glyph B d) := oil P c 0 x • W.pre p c x 0
  let Y : Finset (Glyph B d) := Finset.univ.erase j
  let Z := W.pre p j x 0
  let T := motto p P x 0
  let U := T + ∑ i ∈ Y, f i
  have he : A0 = Z + U := by
    unfold A0 scoreW U T
    rw [Pi.add_apply, add_left_comm, add_comm]
    congr 1
    unfold rentW
    simp_rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    change ∑ c, f c = Z + ∑ c ∈ Y, f c
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ j)]
    unfold f oil
    rw [h.Single j (le_refl _), if_pos rfl, Polynomial.eval_one, Complex.ofReal_one]
    rw [one_smul]
  have hr : Limit T.val ((j.grade : ℤ) - 1) := by
    have hl := h.Low x
    let Q := (P 0).proof
    have hh : T = Menus.advance (Q.input x) := by
      simp only [T, sky, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, style, whoZero]
      rfl
    rw [hh]
    exact
      Limit.add (Limit.up (lapLimit hl) (by omega))
        (Limit.up (rootLimit (participates G 0) hl) (by omega))
  have hi i (hi : i ∈ Y) : Limit (f i).val ((j.grade : ℤ) - 1) := by
    rcases lt_or_ge i.grade j.grade with hI | hI
    · exact Limit.up (Limit.smul _ (W.pre_leg p i 0 x)) (by omega)
    unfold f oil
    rw [h.Single i hI, if_neg (Finset.mem_erase.mp hi).1, Polynomial.eval_zero, Complex.ofReal_zero,
      zero_smul]
    exact fun _ _ => rfl
  have hL : Limit U.val ((j.grade : ℤ) - 1) := by
    refine Limit.add hr ?_
    rw [Cylinder.sum_stack]
    exact Limit.sum _ hi
  rw [show scoreW W p P x 0 = _ from he]
  refine
    ⟨Limit.add
        (by
          convert W.pre_leg p j 0 x using 1
          simp)
        (Limit.up hL (by omega)),
      ?_⟩
  suffices ht : Fits U 0 j.grade j.size false from
    by
    rw [← add_zero j.read]
    exact (W.start p j x).add ht
  unfold Fits
  rw [maskOff (by omega) (Tone.oneRank hL)]
  exact face_zero _

lemma zerosOrderW (p : Team) (h : FitOrder j (P 0)) (x : ℝ) :
    let U := rowFull W p P 0 x;
    Rank U j.grade ∧ ∀ t, Lifting.Face wfield (Book.mask j.grade (U t)) j.read j.size false := by
  intro U
  let M := (feeds W p P)
  obtain hz := M.recu 0 x
  obtain hx := cap0W W p h x
  change U 0 = _ ∧ _ at hz
  have hv : Wind.Near false U := by
    obtain ⟨r, hr⟩ := (M.owes 0).pay
    refine ⟨((M.owes 0).stay x).joint, ⟨r, hr x⟩, fun t w _ => ?_⟩
    have hl := hz.2 t w
    simpa only [Pi.add_apply, Wind.path, Domain.paths, Finset.Ico_self, Finset.sum_empty, smul_zero,
      Pi.zero_apply, add_zero] using hl
  obtain ⟨h0, hg⟩ := Dprecise hv (r := j.grade) (hz.1 ▸ oneRank hx.1)
  refine ⟨h0, fun t => ?_⟩
  rw [show Book.mask _ (U t) = Book.mask _ (U 0) from ?_, hz.1]
  exact hx.2
  funext w
  by_cases he : (w.length : ℤ) = j.grade
  simp only [enough _ he, hg w he]
  simp only [strange _ he]

def trioW (j : Glyph B d) (p : Team) : Knobs (Tactic0 j) G
    where
  wake P := (seekW W p d).wake (clockM j P)
  stay _ _ _ h := (seekW W p d).stay _ _ _ (fun i hi => congr_arg Subtype.val (h i hi))

lemma guardedW (p : Team) (hx : FitOrder j (P 0)) (h : PhysicalHF j F) (hr : j.grade ≤ r) (ht : u ≤ d)
    (H : Disc false 0 S F 1 d) (y : ℝ) : slice ((seekW W p d).wake P 0 - F 0) false r u y = 0 := by
  refine excuse (F := (seekW W p d).wake P) ?_ ?_ ?_ ht y
  · intro x w hw i H
    let L := (seekW W p d).wake P
    have hh := zerosOrderW W p hx x.1
    obtain h1 | h1 := lt_or_eq_of_le hr
    · rw [torch_piece w hw (L 0 x), torch_piece w hw (F 0 x),
        maskOff (v := r) (by omega) (show Limit (L 0 x) j.grade from hh.1 (exp x.2)),
        maskOff (u := j.grade) (by omega) (h.too x)]
    have hc : Form j.read wfield (j.size : ℤ) false :=
      (lease_one.mp (lease_enough G ((Ensure.deck G).le ((Ensure.deck G).form _ _ _)))).2.1
    rw [← h1] at hw
    rw [torch_piece w hw (L 0 x),
      face_here
        (show Lifting.Face wfield (mask j.grade (L 0 x)) j.read j.size false from hh.2 (exp x.2))
        (w := w) (fun u => Bool.noConfusion u) i
        (by
          rw [h.owns]
          exact H),
      torch_piece w hw (F 0 x), h.top, hc.const_term w (fun v => Bool.noConfusion v)]
  · exact fun x w => ((feeds W p P).owes 0 |>.stay x.1).joint.routine _ _
  exact fun x w =>
    (H.master.road ℝ (ray w) 0 (Nat.zero_le _) (fun v => Bool.noConfusion v)
          (fun v => Bool.noConfusion v)).1
      x

theorem physicalW (h : G.Simple) (hq : Fixed (col (skyline G p)) F true 4 1)
    (hh : Disc false 0 F S 1 d) (hx : PhysicalHF j S) :
    ∃ A : Acts (Ensure.deck G) d, FitOrder j (A 0) ∧ Fixed (col (rowFull W p A)) S false d 0 := by
  let K := trioW W j p
  let W₀ := seekW W p d
  let U := Tactic0 j
  let V0 := col (skyline G p)
  let T := mark_seekW W (p := p) (d := d) h
  have HT (i : Code U) : Spheres wave (spaceL G) V0 (K.wake i) 1 0 false := T.law _
  suffices he : ∃ i : Code U, Fixed (K.wake i) S false d 0
    by
    obtain ⟨i, hi⟩ := he
    exact ⟨clockM _ i, (i 0).property rfl, hi⟩
  refine
    assigned («B» := fun _ => V0) HT hh.master hh.good (fun i => T.occurs (clockM j i)) hh.open' ?_
      (by omega) ?_ (script j)
  · intro X n hn hp i hi r
    exact
      hq (n - i)
        (by
          obtain he := path_in hi
          omega)
        _ (fun _ => Nat.succ_pos r)
  intro n hn r hr u hu hv X EE HE
  let M := K.wake X n - S n
  let J := slice M false r u
  have hz := advanced (HT X) hh.master hn hr EE
  by_cases hk : n = 0 ∧ j.grade ≤ r
  · obtain ⟨rfl, H⟩ := hk
    refine ⟨X, Move.refl J ?_⟩
    intro i w _ hx'
    change slice _ _ _ _ _ _ = _
    exact congr_fun (guardedW W p (P := clockM j X) ((X 0).property rfl) hx H hv hh i) w
  have ht : Ready J := slice_ready hz hv (Ready.sub ((HT X).poly n) (hh.master.poly n))
  have hu' (i : ℝ) : J i ∈ Lease G u r 0 :=
    lease_one.mpr
      ⟨slice_solid hz hv fun t => ((HT X).trueC n t).sub (hh.master.trueC n t), slice_form hz hv,
        rank_slice⟩
  have hL (i : ℝ) : natQ (J i) = 0 :=
    funext (fun l => closes (HT X) hh.master hh.good hn hr EE hv HE i l (fun v => Bool.noConfusion v))
  obtain ⟨a, g, h0, h1, hJ, hI, he⟩ := mark_inter ht hu' hL (Ensure.deck G)
  obtain ⟨Q, T, hQ, hT, hW⟩ := BMenu.room (n := n) W p (clockM j X) hu hv h0 h1 hJ hI
  let P := Menus.patch (clockM j X) Q T n
  have he' : FitOrder j (P 0) := fix_order (P := clockM j X) ((X 0).property rfl) hQ hT.le (by omega)
  let Y : Code U := fun i => ⟨P i, fun h => h ▸ he'⟩
  have hm : ∀ i < n, (X i) = (Y i) := fun i hi => Subtype.ext (hW.past i hi)
  refine
    ⟨Y,
      Move.replace
        (rewind (K := K) rfl rfl hm (fun i => (((feeds W p (clockM j X)).owes n).stay i).joint)
          (fun i => (((feeds W p P).owes n).stay i).joint) (recognition W hW))
        (fun i w hw hI => congr_fun (congr_fun he i) w)⟩

open Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans Hem Mell Motif Literal Halo
  Alps Native Outlook High Detect Lifting Local.Physical Mach Train Pearl Emit Wind Wind.Leading Menus
  Program Knobs Land

structure Installed (V : BasisMenu G) {A : Booked (Ensure.deck G)} (M : MS_Data G A)
    (S : Land.Prescription B) : Prop where
  bulk : Fixed (col (skyline G S.team)) (Archive 4 M.bulk) true 4 1
  mark (d : ℕ) (i : Plaid B d) :
    Fixed (col (rowFull V S.team (S.fees d i))) (Archive d (M.marks d i)) false d 0

theorem can_install (V : BasisMenu G) (h : G.Simple) {A : Booked B} (X : MS_Data G A) :
    ∃ S : Land.Prescription B, Installed V X S := by
  obtain ⟨p, hp⟩ := leader_M h B A X
  have he d (i : Plaid B d) :=
    physicalW V (j := Land.read i) h hp
      (Outlook.fieldD X.bulkOK (X.markOK d i) wisdom ((A.law d i).moodQ))
      (Mach.initialHF (A.law d i) (sizeG i) (X.markOK d i))
  choose S hs h using he
  exact ⟨⟨p, S, hs⟩, ⟨hp, h⟩⟩
end YM.WilsonMS.BMenu
