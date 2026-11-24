import YM.WilsonMS.Calibration.Timing
/-!
# Expose the canonical-change residual on the physical source-dependent object

Importantly we exhibit BOTH series with the AFTER relaxation estimates. This
step doesn't assume smallness on a diagonal limit. Same Deck & `team` as
for the uncorrected dictionary if desired. The `Judge` interface adapted from
`Tide.Coi` proof; here we also output charge on the SOURCE-dependent remainder.
The second CCOrb has canonical generators still attached. The eventual EXACT
equality used in that proof is between *two already period-removed answers*
at same separations, not claiming the marked canonical change vanishes at
finite period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS MS.Fleet
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Swirl Swirl.Near SpaceOut Menus Echo Tide
open scoped Topology ContDiff Interval
variable {W I : Type} {P : Geo I} {V : Visa I} {L : I → Side} {x : Faces I} {G : Gauge} {b : Bool}
  [LinearOrder W] {M : Land.Booked (Ensure.deck G)} {t : Team} {F : Finset W}
  {φ : BasisMenu G} {A : Land.Prescription (Ensure.deck G)} {S : MS_Data G M} {n : ℕ}
  (u : W → Label (Ensure.deck G)) (c : Berth (W := W) (I := I)) {l : Filter I} {X : Rake.Dance G I W}
  {Z : Terrify W I}

abbrev fieldSeries (V : BasisMenu G) (t : Team) (a : Land.Prescription (Ensure.deck G))
    (u : W → Label (Ensure.deck G)) : W → Actor G := fun i =>
  rentW V t (a.fees (u i |>.h) ((u i).item))
set_option quotPrecheck false
local notation "Yr" => fieldSeries φ A.team A u
local notation "Ur" => fieldSeries φ (Stripped A.team) A u
local notation "Qa" => goalsK c P.η Yr
local notation "Qr" => goalsK c P.η (PortFull φ A ∘ u)
local notation "φX" => PortFull φ A ∘ u

omit [LinearOrder W] in
lemma ready_both (h : G.Simple) :
    ReadyP A.team Yr ∧ ReadyP A.team φX ∧ Changes Yr Ur A.team ∧ ∀ w, Menu A.team ((φX) w) (Yr w) := by
  refine
    ⟨⟨fun _ => circleRent .., fun w x => untouched φ A.team _ h x⟩,
      ⟨fun _ => circleScore .., fun w x => properShift φ A.team _ h x⟩, fun w x => mechanical ..,
      fun w => ?_⟩
  let X := u w
  let K := A.fees X.h X.item
  refine
    ⟨⟨Menus.prim K,
        ⟨(fun i y => (K i).proof.actual y), (fun i => ⟨_, (K i).proof.ranks⟩), fun i y =>
          (K i).proof.calm y, fun i => (K i).proof.polyn, fun _ _ h => Bool.noConfusion h⟩,
        ?_⟩⟩
  intro y
  change Menus.motto A.team K y = scoreW φ A.team K y - rentW φ A.team K y
  rw [scoreW]
  abel

theorem anchored (hc : G.Simple) (hp : Clearance L x) (he : Vista.width L x) (hm : WidthW V P.η c)
    (ht : Mesh P (info c)) (hv : Sparse l c) (b : Bool) (hV : Installed φ S A) :
    ∃ (Z Z' : Terrify W I) (X : Rake.Dance G I W),
      CCOrb G P.η A.team x L Qa b Z ∧
        CCOrb G P.η A.team x L Qr b Z' ∧
          (∀ i s,
              PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w => c w i) (x i) Ur (bury i s Z)) ∧
            DOrd M P S u (info c) X ∧
              Judge P c V Z (toZ X) L l (Label.h ∘ u) ∧
                (∀ s : Finset W,
                    s.Nonempty → ∀ n, Verdict P (Vane.charge (Label.h ∘ u) s) 0 (X s n)) ∧
                  ∀ (W : ℝ) (μ : ℝ),
                    NearPlan l P V L μ → ∀ s : Finset _, ∀ n, PeakT l P W (Z s n - Z' s n) := by
  obtain ⟨hK, hP, H, hmenu⟩ := ready_both u (φ := φ) (A := A) hc
  have ha : FlowSet V Qa := moneyM c hm (fun i => ⟨false, 0, hK.badge i⟩)
  have hd : FlowSet V Qr := moneyM c hm (fun i => ⟨false, 0, hP.badge i⟩)
  let t := A.team
  obtain ⟨F, f, hF, hf, hT, h0, hpay⟩ := Ωgo (P := x) hV.bulk ha hm.proper b hp he
  obtain ⟨Z, X0, hZ, hZ', hX, h', hx⟩ := Ωgo (P := x) hV.bulk hd hm.proper b hp he
  obtain ⟨U', D, hU, hD, hr⟩ := BMenu.covers φ P A S u hc ht hV
  have hUe : U' = voyage c Z := Rake.perfect hU (boardingA c hZ (Fleet.fee hZ hd))
  have hΩ (s : Finset W) (hp : s.Nonempty) (n : ℕ) : toZ Z s n = toZ U' s n := by
    funext i
    let v (t : ℝ) := (Z s n) i (exp t) []
    have he : (fun t : ℝ => U' s n i t []) = v := funext fun t => by rw [hUe, τv]
    obtain HT := (hX s n i).comp tendsto_exp_atTop
    obtain HH := hr s hp n |>.1.1 i
    change Tendsto (fun t : ℝ => U' s n i t []) _ _ at HH
    rw [he] at HH
    exact tendsto_nhds_unique HT HH
  have hEvent (n : ℕ) (s : Finset W) : toZ F s n =ᶠ[l] toZ Z s n := by
    let a (i : I) (s : Finset W) (n : ℕ) := toZ Z s n i
    let v i s n := toZ F s n i
    exact
      Filter.EventuallyEq.symm
        (Tide.peaks (l := l) (X := a) (Y := v) (marked W) Toy (pointed _ (Tide.zeroZ hZ.1))
          (fun i => fun s _ n _ => Submodule.mem_top) (pointed _ (Tide.zeroZ hF.1))
          (fun i s _ n _ => Submodule.mem_top)
          (fun s n => Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n)
  refine
    ⟨f, X0, D, hf, hZ', fun i s => κglyph c i hK.badge hf (fun _ => circleRent ..) H, hD,
      ⟨⟨h0, Tide.zeroZ hD.1⟩,
        ⟨toZ Z, toZ F, Tide.zeroZ hZ.1, Tide.zeroZ hF.1, fun s hs n => ?_, hpay, hEvent⟩⟩,
      fun s hs n => hr s hs n |>.2.1, ?_⟩
  · rw [hΩ s hs n]
    obtain ⟨h, hv, hu⟩ := hr s hs n
    exact ⟨marketV h hv hu, h.2.2⟩
  intro y μ B s n
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, h0, h', sub_self]
    exact PeakT.zero
  have ht := B.costG (hpay s hs n) y
  have hh := B.costG (hx s hs n) y
  have hb : PeakT l P y (-(X0 s n - toZ Z s n)) := by
    obtain ⟨c, hc, h⟩ := hh
    refine ⟨c, hc, h.mono ?_⟩
    intro i hi
    rw [Pi.neg_apply, norm_neg]
    exact hi
  apply PeakT.fromζ (ht.plus hb)
  filter_upwards [hEvent n s] with i hi
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, hi]
  abel

local notation "g" => (Label.h ∘ u)
local notation "Δ" => lifted P c
open MS.Port
variable (h : G.Simple) (hp : Installed φ S A) {μ : ℝ}
include h hp

lemma phase_read (he : Clearance L x) (hs : Vista.width L x) (hu : WidthW V P.η c)
    (hm : Mesh P (info c)) (hz : NearPlan l P V L μ) (b : Bool) :
    ∃ (Z Z' : Terrify W I) (Y : Rake.Dance G I W),
      (Z ∅ = 0 ∧
          Z' ∅ = 0 ∧
            toZ Y ∅ = 0 ∧
              ∀ i s,
                PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w => c w i) (x i) Ur (bury i s Z)) ∧
        DOrd M (frameF I μ) S u Δ Y ∧
          (∀ s : Finset W, s.Nonempty → ∀ n, Verdict (frameF I μ) (Vane.charge g s) 0 (Y s n)) ∧
            (∀ s n,
                PeakT.twin l P mildG (fare g P Z s n) (Fleet.toZ Y s n) ∧
                  PeakT.twin l P mildG (fare g P (PeakT.ordZ Z) s n) (PeakT.ordZ (Fleet.toZ Y) s n)) ∧
              CCOrb G P.η A.team x L Qr b Z' ∧ (∀ a : ℝ, ∀ s n, PeakT l P a (Z s n - Z' s n)) := by
  obtain ⟨Z, Z', X, hO, hc, hB, hD, hK, hY, hr⟩ :=
    anchored u c h he hs hu hm (payTune c hm hz.vanish) b hp
  obtain ⟨_, Y, _, hJ, hV⟩ := BMenu.covers φ (frameF I μ) A S u h (posed c hm) hp
  have hZ : fare g P (toZ X) = toZ Y :=
    clockShape P Δ u hz.dimm hJ
      (by
        rw [← re_n]
        exact hD)
      (fun s hs n => hV s hs n |>.2.1.1)
  have ht (s : Finset W) (n : ℕ) :
    PeakT l P mildG (fare g P Z s n - toZ Y s n) ∧ PeakT l P 0 (Fleet.toZ Y s n) := by
    refine ⟨hZ ▸ dealP c hK hz, ?_⟩
    by_cases hs : s.Nonempty
    exact Tide.Verdict.economic _ _ (hV s hs n |>.2.1.2.2)
    rw [Finset.not_nonempty_iff_eq_empty.mp hs, Tide.zeroZ hJ.1]
    exact PeakT.zero
  refine
    ⟨Z, Z', Y, ⟨hK.blanks.1, ?_, Tide.zeroZ hJ.1, hB⟩, hJ, fun s hs n => hV s hs n |>.2.1, ?_, hc,
      fun a => hr a μ hz⟩
  · obtain ⟨f, V, hX, hv⟩ := hc
    funext i n
    have h := hv ∅ i n
    rw [((hX n) |>.2.1)] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  intro s n
  refine ⟨(ht s n).symm, ?_⟩
  rw [← funext (fun i => PeakT.ν_norm g (s := s) (P := P) (n := n) i Z)]
  exact PeakT.projection ht s n
end YM.WilsonMS.BMenu
