import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land
/-!
# Loop-weight selection rule

The offset is `r+n` for a source of at least r classical legs at order n,
`2+n` unmarked. Actual number of legs differs from the offset by
**twice** a nonnegative integer. We can keep the full selection rule, even
on the trajectory coming out of the dimensionally-continued high-mode flow.
No assumption here that the later Wilson coefficients of the source are literal
(hh^0) untouched at nonlinear orders from this selection rule alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank
open MS Function Filter Set Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
  _root_.YM.MS.Shine
open Hem Mell Logarithm Pearl Train Signal Book Convolve Garment.Wave Garment.Wick Dock
open scoped Topology ContDiff Interval

/-- Allowed number of legs or coupling power increment. Arguments offset, actual. -/
def Allows (k l : ℕ) : Prop :=
  ∃ i : ℕ, l + 2 * i = k

namespace Allows
variable {a b c d : ℕ}

lemma equal (a : ℕ) : Allows a a :=
  ⟨0, rfl⟩

lemma smaller (h : Allows b a) : a ≤ b := by
  obtain ⟨i, h⟩ := h
  omega

lemma paid (h : Allows b a) (hq : Allows a c) : Allows b c := by
  obtain ⟨i, h⟩ := h
  obtain ⟨j, hq⟩ := hq
  exact ⟨i + j, by omega⟩

lemma sum (h : Allows b a) (hq : Allows d c) : Allows (b + d) (a + c) := by
  obtain ⟨i, h⟩ := h
  obtain ⟨j, hq⟩ := hq
  exact ⟨i + j, by omega⟩

lemma down (h : Allows a (b + 2)) : Allows a b := by
  obtain ⟨i, h⟩ := h
  exact ⟨i + 1, by omega⟩

lemma linear (h : Allows (a + c) (b + c)) : Allows a b := by
  obtain ⟨i, h⟩ := h
  exact ⟨i, by omega⟩
end Allows

abbrev pays {I : Type} (i : ℕ) (F : Raw I ℂ) : Prop :=
  ∀ l, ¬Allows i l.length → F l = 0

section parchment
variable {I : Type} {i j : ℕ} {F H : Raw I ℂ}

lemma full (h : Book.rank i F) : pays i F := fun l ht =>
  h l
    (by
      rw [mod_int]
      intro hx
      replace hx : l.length = i := by omega
      rw [hx] at ht
      exact ht (.equal i))

lemma sum (hf : pays i F) (hh : pays i H) : pays i (F + H) := fun l hp => by
  rw [Pi.add_apply, hf l hp, hh l hp, add_zero]

lemma sums {W : Type} {X : W → Raw I ℂ} (s : Finset W) (hx : ∀ i' ∈ s, pays i (X i')) :
    pays i (∑ k ∈ s, X k) := by
  intro l h
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun k hk => hx k hk l h)

lemma scales (h : pays i F) (z : ℂ) : pays i (z • F) := fun l hp => by
  rw [Pi.smul_apply, h l hp, smul_zero]

lemma higher (h : Allows j i) (hp : pays i F) : pays j F := fun l hx =>
  hp l (fun ht => hx (h.paid ht))
end parchment

section MSData
variable {G : Gauge} {h k l s r n : ℕ} {V Z : Mob G}

def pouch (G : Gauge) (k : ℕ) : LeanC G
    where
  carrier := setOf fun v => ∀ m, pays k (v m)
  zero_mem' := fun _ _ _ => rfl
  add_mem' hf hh := fun i => sum (hf i) (hh i)
  smul_mem' c _ h := fun i => scales (h i) c

lemma asks : V ∈ pouch G k ↔ ∀ i, pays k (V i) :=
  Iff.rfl

lemma passes (G : Gauge) (k : ℕ) : Need (pouch G k)
    where
  touch := by
    intro i l H f P hu hp
    change P ∈ pouch G k
    apply asks.mpr
    intro m u hv
    apply tendsto_nhds_unique (hu m u)
    apply Tendsto.congr' _ tendsto_const_nhds
    exact hp.mono fun i hi => (asks.mp (show f i ∈ pouch G k from hi) m u hv).symm
  walk x s
    hx := by
    replace h : ∀ i, pays k (x i) := asks.mp hx
    change plow _ _ x ∈ pouch G k
    apply asks.mpr
    intro m l ht
    simp only [plow, h m (sr s l) (by simpa [sr] using ht), mul_zero]
  runner := by
    intro F r ht h
    replace h : ∀ s, F s ∈ pouch G k := h
    change mend F r ∈ pouch G k
    apply asks.mpr
    intro n l hu
    unfold mend
    simp_rw [asks.mp (h _) n l hu]
    simp

lemma by_arbor {U : Rip G} (h : reverseF U) (hV : V ∈ pouch G k) (hZ : Z ∈ pouch G l)
    (hl : k + l = r + 2) : arbor U V Z ∈ pouch G r := by
  refine asks.mpr fun i w H => ?_
  unfold arbor tree
  rw [scatter_congr _ _ _ (fun _ _ => (0 : ℂ)) ?_]
  exact map_zero (allocate ..)
  intro u v ht
  rw [convertR (h i)]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  unfold radius
  dsimp only
  obtain hz := split_length ht
  by_cases hL : Allows k (u.length + 1)
  swap
  · rw [asks.mp hV i _ (by simp [hL])]
    simp
  rw [asks.mp hZ i _ ?_, mul_zero]
  simp only [List.length_cons]
  intro hc
  apply H
  apply Allows.linear (c := 2)
  convert hL.sum hc using 1 <;> omega

lemma by_ocean {U : Rip G} {i : ℂ} {b : Bool} (hp : Form0 b V) (ht : Knot b U) (hx : i ∈ Town)
    (he : V ∈ pouch G k) : ocean i U V ∈ pouch G k :=
  asks.mpr fun n l H =>
    (roof_ocean (b := b) (c := false) hp ht (i := l.length)
          ⟨fun m p hz _ =>
            asks.mp he m p
              (fun a =>
                H
                  (show Allows k (l.length) from
                    Allows.down
                      (by
                        rw [show l.length + 2 = p.length from (by omega)]
                        exact a)))⟩
          hx).passes
      n l rfl (fun v => Bool.noConfusion v)

abbrev Carry (k : ℕ) (V : Flats G) :=
  SeedP (fun f => To f (pouch G k)) V
variable {J P : Flats G} {b : Bool} {f p : Coat G} {q t e : ℤ}

lemma ignite (hx : ClockD b q t P) (hp : Carry k P) : Carry k (step0 G P) := by
  refine (washed (pouch G k)).pipe _ _ _ (fun i => ?_)
  filter_upwards [sunny (clockMoon hx i), hp i, high0] with s hs ht hu
  rw [swamp_spec (c_bo 0) hs hu]
  exact (pouch G k).smul_mem _ (by_ocean hs (c_bo 0) hu ht)

lemma heat (he : Carry k P) (ht : Carry l J) (hq : k + l = r + 2) : Carry r (drive0 G P J) :=
  (washed (pouch G r)).explo _ P J
    (fun i j => ((he i).and (ht j)).mono fun _ hr => by_arbor (reverse_a G 0) hr.1 hr.2 hq)

lemma engine (hv : ClockD b q t P) (ht : Vibe n P J) (he : Return P f n) (hp : Stay n J)
    (hx : Carry k P) :
    ∃ Y : Flats G, ∃ p : Coat G, Joint n J Y f p ∧ ClockD b q t Y ∧ Cap0 b q t p ∧ Carry k Y := by
  obtain ⟨m, hH⟩ := tallP (Moony.toast (clockMoon hv))
  obtain hz := correspondent hH ht hp
  let v := Mint m P
  let Q := P - Finsupp.single 0 v
  have hQ := mintCap hv hH
  have hy : Count v n := minted_home hH ht hp
  have hF : ClockD b q t Q := fun i => (hv i).sub (Cap0.heap.single hQ 0 i)
  refine
    ⟨Q, -v,
      { advance := ?_, toll := hz, wet := Moony.toast (clockMoon hF), back := fun i => (hy i).neg,
        ice := ?_, worth := hQ.fine.tune.mer.neg, sip := ?_ },
      hF, hQ.neg, ?_⟩
  · simpa only [sub_zero] using vibe_sub ht (vibe_root hy)
  · exact (cone G).neg_mem (minted m P)
  · simpa only [sub_eq_add_neg, Q] using sip_sub he (sip_root hy)
  have H := MintC hH (pouch G k) (passes G k) hx
  intro i
  exact
    ((hx i).and ((washed (pouch G k)).single (Eventually.of_forall H) 0 i)).mono fun s hs =>
      (pouch G k).sub_mem hs.1 hs.2

lemma runway (h : Coal b n q t J) (hp : Count f n) (hv : Cap0 b q t f) (hq : Carry k J)
    (hU : To f (pouch G k)) :
    ∃ X : Flats G, ∃ p : Coat G, Joint n J X f p ∧ ClockD b q t X ∧ Cap0 b q t p ∧ Carry k X := by
  obtain ⟨H0, H1, H2⟩ := scooter h.eye h.force
  let V := wheels J n + Finsupp.single 0 f
  have H : Vibe n V J :=
    (by
      unfold V
      simpa only [add_zero] using vibe_plus H0 (vibe_root hp))
  have Hx : Return V f n :=
    (by
      unfold V
      simpa only [zero_add] using sip_plus H2 (sip_root hp))
  refine
    engine (Cap0.heap.plus H1 (Cap0.heap.single hv 0)) H Hx h.real
      ((washed (pouch G k)).plus (fun i => ?_) ((washed _).single hU 0))
  rw [loopy]
  filter_upwards [hq i, (h.eye i).fine.tune.mer.price, vamp_up n i] with w hw hH HZ
  exact Mell.road _ (passes G k) hw hH HZ

lemma factories (m : ℕ) (hh : t ≤ (m : ℤ)) (he : Coal b n q t J) (hv : Count f n) (hp : Cap0 b q t f)
    (hQ : Carry k J) (hf : To f (pouch G k)) :
    ∃ X : Flats G, ∃ p : Coat G, Bob b n q t J X f p ∧ Carry k X := by
  induction m using Nat.strong_induction_on generalizing t J f with
  | h m ih =>
    obtain ⟨V, p, Ht, H, pH, hV⟩ := runway he hv hp hQ hf
    obtain hm := mine H Ht.toll
    by_cases hy : t < 2
    · refine ⟨V, p, ⟨Ht.via ?_, H, pH⟩, hV⟩
      have hp := pact0 (F := step0 G V) ⟨_, (by omega : t - 2 < 0), clockCap hm.eye⟩
      refine pact_sym (fun i => ?_)
      filter_upwards [hp i] with j hj
      simp only [Finsupp.add_apply, Pi.add_apply, hj, Finsupp.zero_apply, Pi.zero_apply, add_zero]
    obtain ⟨W, f', ⟨hE, hF, hp⟩, ht⟩ :=
      ih (m - 1) (Nat.sub_one_lt (by omega)) (show t - 2 ≤ ((m - 1 : ℕ) : ℤ) by omega) hm (f := 0)
        (fun _ => Home.zero n) Cap0.zero (ignite H hV) ((washed _).zero)
    refine
      ⟨V + W, p + f',
        ⟨?_, Cap0.heap.plus H (clockTrans hF (by omega : t - 2 ≤ t)),
          pH.add (hp.collects (by omega))⟩,
        (washed _).plus hV ht⟩
    obtain ht := Ht.plus hE
    simpa only [add_zero, map_add] using ht

lemma succ (D : Prop) (h : sings b t n f D J P p) (ht : Badge b f n t) (hp : To f (pouch G k))
    (hq : ∃ i, Coal b n t i J) (hJ : Carry k J) : Carry k P := by
  obtain ⟨w, hw⟩ := hq
  obtain ⟨v, hv⟩ := ht.stock
  let l := max w v
  obtain ⟨X, g, ⟨hX, hh, hL⟩, hu⟩ :=
    factories l.toNat (show l ≤ (l.toNat : ℤ) from by omega) (hw.wax (le_max_left w v)) ht.born
      (hv.collects (le_max_right w v)) hJ hp
  obtain ⟨⟨r, hV, hP, hp⟩, ht⟩ := h
  obtain ⟨H, _⟩ := super hX hV (fun _ => EventuallyEq.rfl) EventuallyEq.rfl hh hP
  exact fun i => ((H i).and (hu i)).mono fun k hk => hk.1 ▸ hk.2
end MSData
end YM.WilsonMS.LoopRank
