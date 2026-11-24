import YM.WilsonMS.Columns.StrictMint
/-! # Path evolution holds jets even after removing poles -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.StrictMint
open MS Function Filter Set Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
  _root_.YM.MS.Shine
open Hem Mell Logarithm Pearl Train Signal Book Convolve Garment.Wave Garment.Wick Dock LoopRank
open scoped Topology ContDiff Interval
variable {G : Gauge} {h k i m r n j : ℕ} {V W X : Mob G} {F J P : Flats G} {p t : Coat G} {b : Bool}
  {q d : ℤ}

theorem vault (k r : ℕ) : Heap (G := G) (fun φ => ∀ᶠ i in dotty, EmptyH r k (φ i)) :=
  ⟨Eventually.of_forall (fun _ => bareLen (fun _ _ _ => rfl)), fun _ _ h ht =>
    (h.and ht).mono fun _ hp => addH hp.1 hp.2⟩

lemma watch_add (h : Watch k r F) (hp : Watch k r J) : Watch k r (F + J) :=
  (vault k r).plus h hp

lemma watch_scale (h : Watch k r F) (x : ℂ) : Watch k r (x • F) := fun i =>
  (h i).mono fun _ hp => scaleH x hp

lemma watch_sub (h : Watch k r F) (ht : Watch k r J) : Watch k r (F - J) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ J]
  exact watch_add h (watch_scale ht _)

abbrev Holds (k r : ℕ) (p : Coat G) (F : Flats G) : Prop :=
  Watch k r (F - Finsupp.single 0 p)

private lemma evacuated (hp : ClockD b d q P) (h : Carry r P) : Watch k r (step0 G P) := by
  refine (vault k r).pipe (swamp (A0 G 0)) P 1 ?_
  intro i
  filter_upwards [sunny (clockMoon hp i), h i, high0] with s hs ht hS
  rw [swamp_spec (c_bo 0) hs hS]
  refine scaleH _ (bareLen ?_)
  intro j l hl
  refine
    (roof_ocean (c := false) (i := r) hs (c_bo 0) ?H hS).passes j l ?_ (fun v => Bool.noConfusion v)
  · refine ⟨fun m p hL hv => ?_⟩
    apply asks.mp ht m p
    intro hh
    have ht := hh.smaller
    omega
  omega

lemma Engine (hv : ClockD b d q P) (ht : Vibe n P J) (he : Return P p n) (hp : Stay n J)
    (hx : Carry r P) (h : Holds n r p P) (hL : Live p) (hk : Count p n) :
    ∃ Y : Flats G,
      ∃ t : Coat G, Joint n J Y p t ∧ ClockD b d q Y ∧ Cap0 b d q t ∧ Carry r Y ∧ Holds n r p Y := by
  obtain ⟨m, hH⟩ := tallP (Moony.toast (clockMoon hv))
  obtain hz := correspondent hH ht hp
  let v := Mint m P
  let Q := P - Finsupp.single 0 v
  have hQ := mintCap hv hH
  have hy : Count v n := minted_home hH ht hp
  have hF : ClockD b d q Q := fun i => (hv i).sub (Cap0.heap.single hQ 0 i)
  refine
    ⟨Q, -v,
      { advance := ?_, toll := hz, wet := Moony.toast (clockMoon hF), back := fun i => (hy i).neg,
        ice := ?_, worth := hQ.fine.tune.mer.neg, sip := ?_ },
      hF, hQ.neg, ?_, ?_⟩
  · simpa only [sub_zero] using vibe_sub ht (vibe_root hy)
  · exact (cone G).neg_mem (minted m P)
  · simpa only [sub_eq_add_neg, Q] using sip_sub he (sip_root hy)
  · have H := MintC hH (pouch G r) (passes G r) hx
    intro i
    exact
      ((hx i).and ((washed (pouch G r)).single (Eventually.of_forall H) 0 i)).mono fun s hs =>
        (pouch G r).sub_mem hs.1 hs.2
  rw [Holds, show Q = _ from (rfl : Q = P - Finsupp.single 0 v), sub_right_comm]
  refine watch_sub h ((vault n r).single (Eventually.of_forall ?_) 0)
  intro s
  let R := P - Finsupp.single 0 p
  have hr : ∀ᶠ i in dotty, EmptyH r n (Parade R n 0 0 i) := parade_rank h 0 0 n
  unfold v Mint
  rw [Finset.sum_apply]
  refine sumH _ (fun i hi => scaleH _ (V := Press P i m 0) ?_)
  have hK := press_pick (m := i) hH n 0 0
  rw [posing, add_zero] at hK
  let g := paid m (Parade R n 0 0)
  have hD := (dry (G := G) hL i (Finset.mem_range.mp hi))
  have hP := hK.add (hD.static (-1 : ℂ))
  rw [neg_one_smul, neg_one_smul, neg_zero, add_zero, ← sub_eq_add_neg] at hP
  refine observes (n := i) (f := g) ?_ (hr.mono (fun i hi => scaleH (i ^ m) hi))
  unfold g R
  rw [page_sub, pureP p hk]
  apply hP.congr
  exact Eventually.of_forall (fun i => (smul_sub (i ^ m) (Parade P n 0 0 i) (p i)).symm)

lemma Runway (h : Coal b n d q J) (hp : Count p n) (hv : Cap0 b d q p) (hL : Live p) (hQ : Carry r J)
    (ht : Watch n r J) (hR : To p (pouch G r)) :
    ∃ X : Flats G,
      ∃ t : Coat G, Joint n J X p t ∧ ClockD b d q X ∧ Cap0 b d q t ∧ Carry r X ∧ Holds n r p X := by
  obtain ⟨T, H, H0⟩ := scooter h.eye h.force
  let Q := wheels J n + Finsupp.single 0 p
  have hr : Carry r (wheels J n) := by
    intro i
    rw [loopy]
    filter_upwards [hQ i, (h.eye i).fine.tune.mer.price, vamp_up n i] with w hw hH HZ
    exact Mell.road _ (passes G r) hw hH HZ
  have hx : Return Q p n := by simpa only [Q, zero_add] using sip_plus H0 (sip_root hp)
  apply
    Engine (Cap0.heap.plus H (Cap0.heap.single hv 0))
      (show Vibe n Q J from (by simpa only [Q, add_zero] using vibe_plus T (vibe_root hp))) hx h.real
      ((washed (pouch G r)).plus hr ((washed _).single hR 0))
      (by
        rw [Holds, add_sub_cancel_right]
        exact listens h ht)
      hL hp

lemma Factory (m : ℕ) (hh : q ≤ (m : ℤ)) (h : Coal b n d q J) (hp : Count p n) (hv : Cap0 b d q p)
    (hL : Live p) (hQ : Carry r J) (ht : Watch n r J) (hR : To p (pouch G r)) :
    ∃ X : Flats G, ∃ t : Coat G, Bob b n d q J X p t ∧ Carry r X ∧ Holds n r p X := by
  induction m using Nat.strong_induction_on generalizing q J p with
  | h m ih =>
    obtain ⟨V, t, Ht, H, tH, hV, ht⟩ := Runway h hp hv hL hQ ht hR
    obtain hm := mine H Ht.toll
    by_cases hy : q < 2
    · refine ⟨V, t, ⟨Ht.via ?_, H, tH⟩, hV, ht⟩
      have hp := pact0 (F := step0 G V) ⟨_, (by omega : q - 2 < 0), clockCap hm.eye⟩
      refine pact_sym (fun i => ?_)
      filter_upwards [hp i] with j hj
      simp only [Finsupp.add_apply, Pi.add_apply, hj, Finsupp.zero_apply, Pi.zero_apply, add_zero]
    obtain ⟨W, t', ⟨hE, hF, hp⟩, hu, hW⟩ :=
      ih (m - 1) (Nat.sub_one_lt (by omega)) (show q - 2 ≤ ((m - 1 : ℕ) : ℤ) by omega) hm (p := 0)
        (fun _ => Home.zero n) Cap0.zero Live.zero (ignite H hV) (evacuated H hV) ((washed _).zero)
    have ht' := Ht.plus hE
    refine
      ⟨V + W, t + t',
        ⟨?_, Cap0.heap.plus H (clockTrans hF (by omega : q - 2 ≤ q)),
          tH.add (hp.collects (by omega))⟩,
        (washed _).plus hV hu, ?_⟩
    · simpa only [add_zero, map_add] using ht'
    rw [Holds, Finsupp.single_zero, sub_zero] at hW
    rw [Holds, add_sub_right_comm]
    exact watch_add ht hW

lemma installs (D : Prop) (h : sings b d n p D J F t) (hL : Live p) (ht : Badge b p n d)
    (hR : To p (pouch G r)) (hQ : ∃ q, Coal b n d q J) (hv : Carry r J) (hT : Watch n r J) :
    Holds n r p F := by
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨w, hv'⟩ := ht.stock
  let l := max q w
  obtain ⟨X, u, ⟨hh, hX, hL⟩, hu, hU⟩ :=
    Factory l.toNat (show l ≤ (l.toNat : ℤ) from by omega) (hq.wax (le_max_left q w)) ht.born
      (hv'.collects (le_max_right q w)) hL hv hT hR
  obtain ⟨⟨s, hV, hE, hS⟩, _⟩ := h
  obtain ⟨H, _⟩ := super hh hV (fun _ => EventuallyEq.rfl) EventuallyEq.rfl hX hE
  intro i
  filter_upwards [hU i, H i] with k hk hK
  exact
    (show ((F - Finsupp.single 0 p) : Flats G) i k = ((X - Finsupp.single 0 p) : Flats G) i k from
          congr_arg (· - (Finsupp.single 0 p : Flats G) i k) hK.symm).symm ▸
      hk
end YM.WilsonMS.StrictMint
