import YM.WilsonMS.Calibration.Rebalance
/-!
# Fix the rank 0 unit block

Here even before H sym and at all perturbative orders. This uses the physical
head of the MS computation (no rescale estimate or action ambiguity). The data
are exactly extended, not `head` in place of mark-dependent exponents.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Rider
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Landau Lattice Cylinder Native Lab Book Convolve Program
open Orient Tone Color Paint Wilsonian High Wind Wind.Leading Knobs Menus Land BMenu Trading Bin
  Outlook
open Logarithm Theater Heat Frame City Flux
open scoped Topology ContDiff Interval Classical
variable {G : Gauge}
local notation "B" => Ensure.deck G
section special
variable (v : Plaid (Ensure.deck G) 0) (W : XSpace.Initialize G) (p : Team)

abbrev bareG (v : Plaid B 0) : Acts B 0 := fun i =>
  ⟨fun j => if i = 0 ∧ Land.read v = j then 1 else 0, 0⟩

lemma a_rank : (Land.read v).grade = 0 := by
  change v.fst.val = 0
  have hp := v.fst.isLt
  omega

def c0 : ℂ :=
  MvPolynomial.coeff 0 (ΕData B (Land.read v))

lemma no_size (x : Glyph B 0) : ∃ v : Plaid B 0, x = Land.read v := by
  rcases x with ⟨a, b, x⟩
  obtain rfl : a = ⟨0, by simp⟩ :=
    Fin.ext
      (show a.val = 0 from by
        have hp := a.isLt
        omega)
  exact ⟨⟨b, x⟩, rfl⟩

lemma film_head : ΕData B (Land.read v) = MvPolynomial.C (c0 v) := by
  let X := ΕData B (Land.read v)
  let r (u : Labels.Key G) := Labels.bidegree u
  apply MvPolynomial.ext
  intro n
  by_cases h : n = 0
  · subst n
    simp [c0]
  rw [MvPolynomial.coeff_C, if_neg (?_)]
  apply Classical.byContradiction
  intro hv
  have ht := (Theater.filmBasic B (Land.read v)).2
  change At X (0, (Land.read v).grade) at ht
  rw [a_rank] at ht
  have hh : Finsupp.weight r n = (0, (0 : ℕ)) := (nodeId _ _ |>.mp ht) hv
  obtain hu : n = 0 := by
    ext c
    obtain hp | hp := le_or_gt (n c) 0
    · exact Nat.eq_zero_of_le_zero hp
    exfalso
    let u := Finsupp.single c 1
    have ha : u ≤ n := Finsupp.single_le_iff.mpr hp
    rw [show n = n - u + u from (tsub_add_cancel_of_le ha).symm, map_add, Finsupp.weight_single,
      one_smul] at hh
    obtain hm := congr_arg Prod.snd hh
    change _ + 1 = 0 at hm
    omega
  contradiction
  exact Ne.symm h

lemma Bare_init : FitOrder (Land.read v) (bareG v 0) :=
  ⟨fun _ _ _ => rfl, fun i _ => by simp [eq_comm]⟩

lemma Bare_same : sameH (bareG (G := G)) := by
  intro s i j k
  obtain ⟨p, rfl⟩ := no_size k
  by_cases he : j = 0
  swap
  · rw [ledger]
    simp [he]
  subst j
  rw [ledger]
  have hh (i j : Plaid B 0) : (bareG i 0).register (Land.read j) = if i = j then 1 else 0 := by
    simp only [true_and, (Ensure.read_inj ..).eq_iff]
  rw [Finset.sum_eq_single (Land.read i)]
  · rw [hh, if_pos rfl, Finset.sum_eq_single p]
    · rw [hh, if_pos rfl]
    · intro b _ h
      rw [hh, if_neg h, smul_zero]
    simp
  · intro a _ h
    rw [show (bareG i 0).register a = 0 from if_neg (fun H => h H.2.symm), smul_zero]
  simp

private def stone (n : ℕ) : Wind.Pack G := fun _ _ => if n = 0 then coin (c0 v) else 0

lemma pawns (x : ℝ) (n : ℕ) : scoreW W p (bareG v) x n = if n = 0 then piece (c0 v) else 0 := by
  let c := c0 v
  let J := Land.read v
  let P : Dot G Cover := piece c
  let U := levelGrade W 0 0 (Labels.unit G 0)
  have hq : vertices W J = fun n => if n = 0 then piece c else 0 := by
    have hu : IsEmpty (more J) := by
      refine ⟨fun j => ?_⟩
      have hp := j.2.isLt
      have hx : J.grade = 0 := a_rank v
      omega
    unfold vertices
    rw [Finset.sum_of_isEmpty, add_zero]
    change levels (J.grade : ℤ) (Webs.symbol _ (ΕData _ (Land.read _))) = _
    rw [film_head v, Webs.symbol_C, show J.grade = 0 from a_rank v]
    funext k
    apply Subtype.ext
    split_ifs with hv
    · subst k
      exact (rank_hat 0 |>.mp (Rails.coin c))
    apply
      rank_off (F := coin (A := LightMode G Cover) c) (h := 0) (hx := (k : ℤ) + (↑(0 : ℕ) : ℤ))
        (Rails.coin c)
    omega
  have ht : preambleW W p J x = vertices W J := by
    let V := vertices W J
    let S := fieldV (G := G) p x ∘ Prod.fst (β := Cover)
    have hz : substitute (Program.shift p x) V = V := by
      rw [show V = _ from hq]
      funext n
      rw [rules, Finset.sum_eq_single_of_mem 0 (Finset.mem_Iic.mpr (Nat.zero_le _))]
      · unfold Program.cut
        rw [pow_zero,
          show (if 0 = 0 then piece c else 0) = piece (A := LightMode G Cover) c from if_pos rfl]
        by_cases he : n = 0 <;> simp [he]
      intro n _ h
      rw [if_neg h, smul_zero]
    change car S (substitute _ V) = V
    rw [hz]
    funext n
    by_cases he : n = 0
    · subst n
      simp_rw [rolls, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      apply Subtype.ext
      rw [train_v]
      exact price_mem ..
    unfold V
    rw [hq, rolls]
    simp only [he, ↓reduceIte]
    rw [Finset.sum_eq_single (n, 0)]
    · apply Subtype.ext
      funext l
      rw [if_pos rfl, train_v, offer]
      rcases l with _ | ⟨j, l⟩
      simp [he]
      change _ * (0 : ℂ) = _
      exact mul_zero _
    · intro j hj h
      have hp : j.2 ≠ 0 := by
        intro hb
        apply h
        obtain hx := Finset.mem_antidiagonal.mp hj
        exact Prod.ext (by omega) hb
      rw [if_neg hp, map_zero]
    simp
  rw [scoreW, Pi.add_apply, sky]
  change
    _ +
        ((Spectrum G).Lap (0 : Dot G Cover) +
          (∑ j ∈ Finset.antidiagonal n, (Spectrum G).touch (style G p x j.1) 0)) =
      _
  simp only [map_zero, Finset.sum_const_zero, add_zero]
  unfold rentW
  rw [Finset.sum_eq_single_of_mem (Land.read v) (mem_univ _)]
  swap
  · intro i hi he
    exact
      Finset.sum_eq_zero fun a _ => by
        rw [oil, bareG]
        simp [Ne.symm he]
  rw [Finset.sum_eq_single (0, n)]
  · rw [oil, bareG]
    simp only [and_self, ↓reduceIte, Polynomial.eval_one, Complex.ofReal_one, one_smul]
    rw [ht, hq]
  · intro j hj he
    have hp : j.1 ≠ 0 := fun h =>
      he
        (Prod.ext h
          (by
            obtain hx := Finset.mem_antidiagonal.mp hj
            omega))
    simp [oil, hp]
  simp

lemma frozen : rowFull W p (bareG v) = stone v := by
  let V := rowFull W p (bareG v)
  let F := skyline G p
  have hV := feeds W p (bareG v)
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let J := stone v n
    funext x
    apply sub_eq_zero.mp
    let U := V n x - stone v n x
    have hU : U 0 = 0 := by
      unfold U
      rw [Pi.sub_apply, show V n x 0 = _ from (hV.recu n x).1, pawns]
      split_ifs with h <;>
        (first
          | ( rw [show run _ = coin (c0 v) from coin_turn ..]
              simp [stone, h])
          | simp [stone, h])
    have ht i (x : ℝ) : TouchF (stone v i x) := fun E _ _ f w hw hv => by
      cases w with
      | nil => by_cases hi : i = 0 <;> simp [stone, hi, walk0] <;> exact contDiff_const
      | cons a l => by_cases hi : i = 0 <;> simp [stone, hi, walk0, coin] <;> exact contDiff_const
    obtain ⟨r, H⟩ := (hV.owes n).pay
    change U = 0
    refine Dtotal (F := U) ⟨?_, ⟨(r : ℤ), ?_⟩, ?_⟩ hU
    · intro E _ _ f w hx hf
      exact ((hV.owes n |>.stay x).joint E f w hx hf).sub (ht n x E f w hx hf)
    · refine Rank.sub (H x) ?_
      intro i l hh
      cases l
      · simp at hh
        omega
      simp [stone]
      split <;> rfl
    intro y l _
    let Jv := path 1 n 0 F V
    have hj : Jv x = 0 := by
      unfold Jv Wind.path
      simp only [one_smul, Finset.sum_apply]
      apply sum_eq_zero
      intro i h
      rw [show V i = _ from ih i (Wind.path_in h |>.2)]
      funext t w
      let C := treeP G
      change Flux.tree parity _ _ _ _ = _
      by_cases hh : i = 0
      · apply (scatter_congr _ _ _ (fun _ _ => 0) ?_) |>.trans
        swap
        · intro i j _
          unfold attaches
          simp [stone, hh, coin]
        exact map_zero (allocate ..)
      change treeP G _ _ _ _ = _
      rw [show stone v i x = 0 from funext (fun t => if_neg hh), map_zero]
    have hb := (hV.recu n x).2 y l
    change HasDerivAt _ (_ + Jv x y l) y at hb
    rw [hj] at hb
    simp only [Pi.zero_apply, add_zero] at hb
    have hh : Wiref G (stone v n x) = 0 := by
      funext t w
      change Heat.orbit _ _ (stone v n x t) w = _
      rw [finite_cc μzone (period0 μzone cour0 (City.main_f G) (ht n x))]
      unfold Ccy
      simp_rw [at_trc, stone]
      split_ifs with he <;> simp [coin]
    unfold U
    rw [map_sub, hh, sub_zero]
    convert! hb.sub_const ((stone v n x 0) l) using 1
open Dock Train Pearl Motif Mach Literal Halo Arts Rock _root_.YM.MS.Shine Path Hem Hem.Mell HBeam
local notation "H" => JRad.book G

abbrev blue (v : Plaid (Ensure.deck G) 0) : Mob G := fun _ => coin (c0 v)

abbrev bank (v : Plaid (Ensure.deck G) 0) : Coat G := fun _ => blue v

lemma interest : (H).optics 0 v = Finsupp.single 0 (blue v) := by
  apply box_unique
  intro z
  rw [JRad.Book_formula G 0 v z, film_head, value_sl, pow_zero, one_smul]
  exact funext fun n => JRad.constV _
variable (T : MS_Data G (JRad.book G))

private def coreU (j : ℕ) : Flats G :=
  if j = 0 then Finsupp.single 0 (bank v) else 0

private def rawF (i : ℕ) : Coat G :=
  if i = 0 then bank v else 0

lemma optical : Emit.gloss (linear (Mob G) ((JRad.book G).optics 0 v)) = rawF v := by
  rw [interest]
  funext i z
  by_cases he : i = 0
  · subst i
    rw [rawF, if_pos rfl]
    exact Finsupp.single_eq_same
  rw [rawF, if_neg he]
  exact Finsupp.single_eq_of_ne he

lemma Verified : Badge false (bank v) 0 0 := by
  obtain hp := Ele.grows ((H).law 0 v) 0
  rw [optical, show rawF v 0 = bank v from if_pos rfl] at hp
  exact hp

lemma bankCap : Cap0 false 0 0 (bank v) := by
  obtain ⟨r, hx⟩ := Verified v |>.stock
  refine ⟨hx.fine, Eventually.of_forall ?_⟩
  intro i n l hl
  rcases l with _ | ⟨a, l⟩
  simp at hl
  rfl

lemma Live_cap : kPrice (blue v) := by
  obtain ⟨x, h⟩ := (bankCap v |>.fine.tune.mer.price).exists
  exact h

lemma verifiedX : comet 0 0 T.bulk (rawF v) (coreU v) 0 := by
  intro j
  have hx : platform T.bulk j (coreU v) = 0 := by
    unfold platform
    apply Finset.sum_eq_zero
    intro k _
    by_cases hp : k.2 = 0
    swap
    · rw [coreU, if_neg hp, map_zero]
    rw [coreU, if_pos hp]
    let U := bank v
    rw [drive0, TreeN, explodeL]
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun n hn => ?_
    have hf (f : Coat G) : tapeB (Oceans.squad (Garment.Wick.A0 G 0)) f (bank v) = 0 := by
      funext z m l
      change Flux.tree _ _ _ (coin (c0 v)) l = _
      apply (scatter_congr _ _ _ (fun _ _ => 0) ?_) |>.trans
      swap
      · intro i j _
        simp [attaches, coin]
      exact map_zero (allocate ..)
    by_cases ht : 0 = n
    · subst n
      rw [Finsupp.single_eq_same]
      simp only [hf, Finsupp.single_zero]
    rw [Finsupp.single_eq_of_ne (Ne.symm ht)]
    simp only [map_zero, Finsupp.single_zero]
  unfold PathD
  rw [hx]
  let F := bank v
  by_cases he : j = 0
  swap
  · rw [rawF, if_neg he, coreU, if_neg he]
    exact zero_sing False
  let Z : Flats G := Finsupp.single 0 F
  have hZ : ClockD false 0 0 Z := Cap0.heap.single (bankCap v) 0
  have hC := (Verified v).born
  have hv : Joint 0 0 Z F 0 :=
    ⟨vibe_root hC, fun x t => by
      rw [show Parade Z 0 x t = bank v from pureP _ hC t x]
      exact Live.stays (Live_cap v), Moony.toast (clockMoon hZ), Submodule.zero_mem _, mer.zero,
      fun x => Home.zero _, by
      rw [add_zero]
      exact sip_root hC⟩
  have hn : Pact (step0 G Z) 0 := pact0 ⟨_, by norm_num, clockCap (mine hZ hv.toll).eye⟩
  rw [rawF, if_pos he, coreU, if_pos he]
  refine ⟨⟨0, ?_⟩, fun h => h.elim⟩
  unfold Bob
  rw [zero_add]
  exact ⟨hv.via (pact_sym hn), hZ, Cap0.zero⟩

lemma matchX : col (rowFull W p (bareG v)) = Archive 0 (T.marks 0 v) := by
  have hp := T.markOK 0 v
  rw [optical] at hp
  let S := coreU v
  have hV := verifiedX v T
  obtain ⟨Y, hY⟩ := unique_M hp hV (fun _ _ => EventuallyEq.rfl)
  rw [frozen]
  funext n z
  rw [show Archive 0 _ n z = four 0 (T.marks 0 v n) z from rfl,
    four_pact (gang (hp n) |>.dost) (gang (hV n) |>.dost) (hY n)]
  by_cases he : n = 0
  · subst n
    obtain ⟨x, y⟩ := z
    have hx : hereZ 0 (S 0) y x = blue v := by
      apply Lift.unique (live0 (gang (hV 0) |>.dost))
      rw [coreU, if_pos rfl, show Parade _ _ _ _ = bank v from pureP _ (Verified v).born y x]
      exact Lift.stays (Live_cap v)
    apply (congr_fun hx 0).symm
  simp only [coreU, if_neg he]
  obtain ⟨x, y⟩ := z
  rw [show four (G := G) 0 0 (x, y) = _ from congr_fun (Outlook.no0 _ _ _) 0]
  exact if_neg he

lemma fixed (hx : G.Simple) (h : Fixed (col (skyline G p)) (Archive 4 T.bulk) true 4 1) :
    Fixed (col (rowFull W p (bareG v))) (Archive 0 (T.marks 0 v)) false 0 0 := by
  obtain ⟨q, hp, hL⟩ :=
    BMenu.physicalW W (j := Land.read v) hx h
      (Outlook.fieldD T.bulkOK (T.markOK 0 v) wisdom (((H).law 0 v).moodQ))
      (Mach.initialHF ((H).law 0 v) (sizeG v) (T.markOK 0 v))
  rw [matchX v W p T]
  intro n h k hk E _ _ w hw hp
  specialize hL n h k hk E w hw hp
  exact
    Like.same (g := Plane.rate High.meet High.eps_gain) (fun i => (Plane.at_start p_gain.le i).1.le)
      hL.std
end special
open Dock

structure Commuting (S : Land.Prescription B) : Prop where
  field_shift (d : ℕ) : sameH (S.fees d)
  unit (v : Plaid B 0) : S.fees 0 v = bareG v

/-- The choice of registering labels is on a filtered basis at all horizons at once.
It preserves H and the unit before any frame computation. -/
theorem Equipped (W : XSpace.Initialize G) (T : MS_Data G (JRad.book G)) (h : G.Simple) :
    ∃ S : Land.Prescription B, Commuting S ∧ Installed W T S := by
  obtain ⟨S, hS⟩ := can_install W h T
  let V (d : ℕ) (i : Plaid B d) : Acts B d := balance (S.fees d) i
  let X (d : ℕ) (i : Plaid B d) : Acts B d :=
    match d, i with
    | 0, i => bareG i
    | d + 1, i => V (d + 1) i
  have hx (d i) : FitOrder (Land.read i) (X d i 0) := by
    cases d with
    | zero => exact Bare_init _
    | succ d => exact economy (S.fees _) _ (S.init _)
  refine ⟨⟨S.team, X, hx⟩, ⟨?_, fun i => rfl⟩, ⟨hS.bulk, ?_⟩⟩
  · intro d
    cases d with
    | zero => exact Bare_same
    | succ d => exact same _
  intro d i
  cases d with
  | zero => exact fixed i _ _ _ h hS.bulk
  | succ d =>
    change Fixed (col (rowFull (↑W : BasisMenu G) S.team _)) _ _ _ _
    exact Rider.purse (G:=G) W T S.team (S.fees (d+1)) i (actsPre W) (hS.mark _)
end YM.WilsonMS.Rider
