import YM.WilsonMS.Columns.PaysProof
import YM.WilsonMS.Calibration.RStone
/-!
# On a curved field table, choose mark adjustments with full order accounting

`TrueAccount` is the parity-controlled version. Need an even stronger
certificate if keeping the strict-power property of field changes;
provided in `PaidLate.earned` for `StrictAccount`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank.MChoice
open MS Function Filter Finset Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open LogTime Domain Local.Physical High Knobs Wind Wind.Leading Menus Land Motif Mach Lifting BMenu
  Rider
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {k i h d : ℕ} (W : BasisMenu G) {p : Team}
  {A : Land.Booked (Ensure.deck G)}
local notation "B" => Ensure.deck G

abbrev Icon (J : Glyph B d) (i : ℕ) :=
  { u : Tact B d // (i = 0 → FitOrder J u) ∧ Controlled (i + J.grade) u }
variable (J : Glyph (Ensure.deck G) d)

def primed (i : ℕ) : Icon J i := by
  by_cases hz : i = 0
  swap
  · exact ⟨0, fun hv => (hz hv).elim, ⟨fun g ht => (ht rfl).elim, fun _ _ _ => rfl⟩⟩
  subst i
  refine ⟨(script J 0).val, (script J 0).property, ?_, fun _ _ _ => rfl⟩
  intro g hg
  change (if g = J then _ else _) ≠ 0 at hg
  rw [show g = J from Classical.byContradiction fun h => hg (if_neg h), zero_add]
  exact Allows.equal _

def cedar (i : Code (Icon J)) : Acts B d := fun n => (i n).val

def here (p : Team) : Knobs (Icon J) G
    where
  wake i := (seekW W p d).wake (cedar J i)
  stay _ _ _ h := (seekW W p d).stay _ _ _ (fun i hi => congr_arg Subtype.val (h i hi))

lemma collected (i : Code (Icon J)) (n : ℕ) : Controlled (n + J.grade) (cedar J i n) :=
  (i n).property.2
open Ghost Cylinder Lab

private lemma pens {u : ℤ} {T : ℝ → Law G} (h : Ready T) (H : ∀ x, T x ∈ Lease G u k (-1)) :
    ∃ P : Power G,
      P.allowance = k ∧ (∀ x, Fits (P.input x) (T x) k u false) ∧ (∀ x, pays k (P.input x).val) := by
  choose F hf hF using fun x => Ghost.voice (H x)
  obtain ⟨N, hN⟩ := h
  let L x i : ℂ := ((plate N i).eval x : ℝ)
  let D : Power G :=
    { input x := ∑ i ∈ Finset.range N, L x i • F i
      polyn := by convert! (eval_ready N F) using 1
      actual x := Tune.sum _ (fun i _ => (hf _ |>.charge).cash _ (by simp [L]))
      calm x := Colorless.csum _ (fun i _ => (hf _ |>.lit).smul _)
      allowance := k
      ranks
        x := by
        rw [sum_stack]
        have he i : Limit (F i).val k := fun l he =>
          hf i |>.level l
            (by
              rw [mod_int]
              omega)
        exact Limit.sum _ (fun i _ => (he _).smul _) }
  refine ⟨D, rfl, fun x => ?_, fun x => ?_⟩
  · rw [interpret hN x]
    unfold evaluate
    rw [show ∑ i ∈ Finset.range N, (plate _ i).eval x • T i = ∑ i ∈ Finset.range N, L x i • T i from
        rfl]
    exact Fits.sum _ (fun i _ => (hF _).smul _)
  dsimp only [D]
  rw [sum_stack]
  exact sums _ fun i _ => scales (LoopRank.full (hf _ |>.level)) _

lemma additional {F H : ℝ → Law G} (P : Acts B d) (p : Team) {v : ℤ} {r : ℕ} (h : 0 ≤ v) (ht : v ≤ d)
    (hp : Ready F) (hq : Ready H) (hc : ∀ i, F i ∈ (B).carries v r)
    (hd : ∀ i, H i ∈ Lease G (v - 1) r (-1)) (hr : Controlled (i + J.grade) (P i))
    (hv : Allows (i + J.grade) r) :
    ∃ Q X,
      Glyph.Homes Q v r ∧
        X.allowance = r ∧
          Ability W p P (Menus.patch P Q X i) i r v (fun j => F j + natQ (H j)) ∧
            Controlled (i + J.grade) (Menus.patch P Q X i i) := by
  obtain ⟨Q, hQ, hF⟩ := Glyph.offered h ht hc hp
  obtain ⟨X, hx, hX, hY⟩ := pens hq hd
  have he (x : ℝ) :
    Limit (Menus.advance (X.input x)).val r ∧
      Fits (Menus.advance (X.input x)) (natQ (H x)) r v false :=
    estimateL x (hx ▸ X.ranks x) (hX x)
  have hA : Ability W p P (Menus.patch P Q X i) i r v (fun i => F i + natQ (H i)) := by
    refine ⟨fun n h => (patch_bef P Q X h.ne).symm, fun x => ?_, fun x => ?_⟩ <;> rw [BMenu.repair]
    exact (shines W p hQ x).1.add (he x).1
    rw [← hF x]
    exact (shines W p hQ x).2.add (he x).2
  refine ⟨Q, X, hQ, hx, hA, ?_⟩
  rw [Menus.patch, if_pos rfl]
  constructor
  · intro a ha
    by_cases H : Q a = 0
    · change (P i).register a - Q a ≠ 0 at ha
      rw [H, sub_zero] at ha
      exact hr.support a ha
    exact (hQ.grade a H) ▸ hv
  intro q t hu
  change ((P i).proof.input q).val t - (X.input q).val t = _
  rw [hr.auxiliary, higher hv (hY q) t hu, sub_zero]
  exact hu
open Dock Outlook

lemma markedW (hR : RankBudget W) (Y : MS_Data G A) (hG : G.Simple) (he : Valid p)
    (hp : Fixed (col (skyline G p)) (Archive 4 Y.bulk) true 4 1) (j : Plaid B d) :
    ∃ Z : Acts B d,
      (∀ i, Controlled (i + (Land.read j).grade) (Z i)) ∧
        FitOrder (Land.read j) (Z 0) ∧
          Fixed (col (rowFull W p Z)) (Archive d (Y.marks d j)) false d 0 := by
  let S := Archive d (Y.marks d j)
  let J := Land.read j
  let K := here W J p
  let F := col (skyline G p)
  have ht (p : Code (Icon J)) : Spheres wave (spaceL G) F (K.wake p) 1 0 false :=
    (mark_seekW W hG).law _
  have hx := Mach.initialHF (A.law d j) rfl (Y.markOK d j)
  have hh := Outlook.fieldD Y.bulkOK (Y.markOK d j) Motif.wisdom ((A.law d j).moodQ)
  suffices ha : ∃ i : Code (Icon J), Fixed (K.wake i) S false d 0
    by
    obtain ⟨q, hq⟩ := ha
    exact ⟨_, (collected _ q), (q 0).property.1 rfl, hq⟩
  refine
    assigned ht hh.master hh.good (fun i => (mark_seekW W (p := p) hG).occurs (cedar J i)) hh.open' ?_
      (by omega) ?_ (primed J)
  · intro X n hn hx i hi r
    exact
      hp (n - i)
        (by
          obtain he := path_in hi
          omega)
        _ (fun _ => Nat.succ_pos r)
  intro n hn r hr u hu hv X EE HE
  let M := K.wake X n - S n
  let T := slice M false r u
  have hz := advanced (ht X) hh.master hn hr EE
  by_cases hk : n = 0 ∧ J.grade ≤ r
  · obtain ⟨rfl, H⟩ := hk
    refine ⟨X, Move.refl T ?_⟩
    intro i w _ hx'
    exact congr_fun (guardedW W p (P := cedar J X) ((X 0).property.1 rfl) hx H hv hh i) w
  let Z := cedar J X
  by_cases hb : Allows (n + J.grade) r
  swap
  · refine ⟨X, Move.refl T ?_⟩
    intro i w _ hw
    rw [show T = 0 from
        Leader.rank_absent (P := K.wake X n)
          (fun i =>
            Pm_b i.1 (feeds W p Z) (skyPC G p) he (score_b W hR he Z J.grade (collected J X) i.1) n
              (exp i.2))
          (mark_archive Y j n) hb]
    rfl
  have hReady : Ready T := slice_ready hz hv (Ready.sub ((ht X).poly n) (hh.master.poly n))
  have hu' (i : ℝ) : T i ∈ Lease G u r 0 :=
    lease_one.mpr
      ⟨slice_solid hz hv fun t => ((ht X).trueC n t).sub (hh.master.trueC n t), slice_form hz hv,
        rank_slice⟩
  have hL (i : ℝ) : natQ (T i) = 0 :=
    funext (fun l => closes (ht X) hh.master hh.good hn hr EE hv HE i l (fun v => Bool.noConfusion v))
  obtain ⟨a, g, h0, h1, hJ, hI, h'⟩ := mark_inter hReady hu' hL B
  obtain ⟨Q, D, hQ, hT, hW, hA⟩ := additional W J Z p hu hv h0 h1 hJ hI (collected J X n) hb
  let P := Menus.patch Z Q D n
  let X' : Code (Icon J) := fun i =>
    ⟨P i,
      (by
        intro he
        subst i
        exact fix_order (P := Z) ((X 0).property.1 rfl) hQ hT.le (by omega)),
      (by
        by_cases Hi : i = n
        subst i
        exact hA
        unfold P
        rw [Menus.patch, if_neg Hi]
        exact (X i).property.2)⟩
  have hm : ∀ i < n, (X i) = (X' i) := fun i hi => Subtype.ext (hW.past i hi)
  refine
    ⟨X',
      Move.replace
        (rewind (K := K) rfl rfl hm (fun i => (((feeds W p Z).owes n).stay i).joint)
          (fun i => (((feeds W p P).owes n).stay i).joint) (recognition W hW))
        (fun i w hw hI => congr_fun (congr_fun h' i) w)⟩
end YM.WilsonMS.LoopRank.MChoice
namespace YM.WilsonMS.LoopRank.MChoice
open MS Function Filter Set Finset MeasureTheory Real
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open LogTime Domain Local.Physical High Knobs Wind Wind.Leading Menus Land Motif Mach Lifting BMenu
  Rider Trading Bin Cylinder Lab Draft Orient
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {k i h d : ℕ} {b : Bool} {P : Prescription (Ensure.deck G)}
local notation "B" => Ensure.deck G
section colours

lemma colour {x : Acts B d} (h : Controlled k (x i)) (s : Signed) : Controlled k (trade s x i) := by
  refine ⟨fun z hv => ?_, fun a l hu => ?_⟩
  · rsuffices ⟨b, hb, he⟩ : ∃ b : Glyph B d, (x i).register b ≠ 0 ∧ b.grade = z.grade
    · exact he ▸ h.support b hb
    by_contra! he
    rw [ledger] at hv
    apply hv
    exact
      Finset.sum_eq_zero fun j _ => by
        by_cases hx : (x i).register j = 0
        rw [hx, smul_zero]
        rw [show lines s j z = 0 from
            Classical.byContradiction fun ht => he j hx (bins s j z ht |>.2),
          zero_smul]
  let X := (x i).proof.input a
  change (pose s X).val l = 0
  let f : Dot G Cover := graffiti (Orient.σ s) X
  change shade _ f l = 0
  rw [← enough (h := (l.length : ℤ)) (F := shade (way (turn s)) f) l rfl, ← mod_ink,
    show Book.model l.length f = 0 from ?_, map_zero]
  rfl
  apply Subtype.ext
  ext u
  by_cases hx : (u.length : ℤ) = l.length
  swap
  · exact strange u hx
  apply Eq.trans (enough (F := f.val) u hx)
  change (u.map (Orient.σ s)).prod * X.val u = 0
  exact mul_eq_zero_of_right _ (h.auxiliary a _ (by rwa [show u.length = l.length from by omega]))

lemma collection {I : Type} (X : Finset I) (F : I → Acts B d) (c : I → ℝ) (a : Acts B d)
    (h : Ticket a X c F) (hv : ∀ i' ∈ X, c i' ≠ 0 → Controlled k (F i' i)) : Controlled k (a i) := by
  refine ⟨fun z he => ?_, fun x => ?_⟩
  · by_contra ht
    refine he ?_
    rw [h.reg, Finset.sum_apply]
    exact
      Finset.sum_eq_zero fun j hj => by
        by_cases hx : c j = 0
        rw [hx, zero_smul]
        rfl
        change c j • (F j i).register z = 0
        rw [show (F j i).register z = 0 from
            Classical.byContradiction fun hm => ht ((hv j hj hx).support z hm),
          smul_zero]
  rw [h.pf, Finset.sum_apply, sum_stack]
  exact
    sums _ fun j hj => by
      by_cases hx : c j = 0
      rw [hx, Complex.ofReal_zero, zero_smul]
      exact fun l _ => rfl
      exact scales ((hv j hj hx).auxiliary x) _

lemma bankP {k i : ℕ} (V : Plaid B d → Acts B d)
    (hv : ∀ v, Controlled (k + (Land.read v).grade) (V v i)) (v : Plaid B d) :
    Controlled (k + (Land.read v).grade) (balance V v i) := by
  refine
    collection _ _ _ _ (balanced ..)
      (fun s _ _ => collection _ _ _ _ (delivering V s v) fun k hk ht => colour ?_ _)
  rw [show (Land.read v).grade = (Land.read k).grade from congr_arg Fin.val (Bin.passes _ _ _ ht)]
  exact hv k

lemma neutral (i : Plaid B 0) (n : ℕ) : Controlled (n + (Land.read i).grade) (bareG i n) := by
  constructor
  · intro g hg
    change (if n = 0 ∧ _ then _ else _) ≠ 0 at hg
    split at hg
    rename_i he
    · rw [← he.2, he.1, zero_add]
      exact Allows.equal _
    contradiction
  exact fun _ _ _ => rfl

structure TrueAccount (P : Prescription B) : Prop where
  acts : Valid P.team
  fees d (j : Plaid B d) i : Controlled (i + (Land.read j).grade) (P.fees d j i)

theorem allotted (W : XSpace.Initialize G) (A : MS_Data G (JRad.book G)) (h : G.Simple) :
    ∃ S : Land.Prescription B, Commuting S ∧ Installed W A S ∧ TrueAccount S := by
  obtain ⟨p, hp, hT⟩ := Leader.oddWaves A h
  choose R hr hK hR using fun d (j : Plaid B d) => markedW W (primaryRank W) A h hp hT j
  let X (d : ℕ) (i : Plaid B d) : Acts B d :=
    match d, i with
    | 0, i => bareG i
    | d + 1, i => balance (R (d + 1)) i
  have hx (d i) : FitOrder (Land.read i) (X d i 0) := by
    cases d with
    | zero => exact Bare_init _
    | succ d => exact economy (R _) _ (hK _)
  refine ⟨⟨p, X, hx⟩, ⟨?_, fun i => rfl⟩, ⟨hT, ?_⟩, hp, ?_⟩
  · intro d
    cases d with
    | zero => exact Bare_same
    | succ d => exact same _
  · intro d i
    cases d with
    | zero => exact Rider.fixed i W p A h hT
    | succ d =>
      change Fixed (col (rowFull (↑W : BasisMenu G) p _)) _ _ _ _
      exact Rider.purse (G:=G) W A p (R (d+1)) i (actsPre W) (hR _)
  intro d i k
  cases d with
  | zero => exact neutral i k
  | succ d => exact bankP _ (fun i => hr _ i k) _
end colours
end YM.WilsonMS.LoopRank.MChoice
