import YM.Integration.WilsonAllDateHarvestPropagation
import YM.RG05Readout.Many.Film

/-! The genuine many-source histories keep the same two endpoints at all dates.
The factor of two is charged at the chosen receiving date only. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestReplay

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open WilsonAllDateHarvestStability WilsonAllDateHarvestAffine WilsonAllDateHarvestLedger
open scoped BigOperators Classical

variable {G:Gauge} {C:Family G} {n b m N p d k:ℕ} {V:ℕ→Type}
variable [∀i,DecidableEq (V i)] [∀i,Fintype (V i)] {W:Type*}
/-- Every mode of the full physical census uses at most the three original
colors, including after the later block regroupings. -/
theorem ward (o:Fin 3→Site (C.side n p)) (E:Fin 3→Motion)
    (roster:Census (Fin 3)) (i:ℕ) : Three (Mine.ward o E roster i) := by
  intro a
  have lit:= (Finset.mem_filter.mp a.property).2
  have count:=Lit.keep_count lit
  have three:=Finset.card_le_univ lit.climb.val
  simpa only [count,Fintype.card_fin] using three

variable (A:Planner C p n V W) (H:∀i,Census (V i)) (s:W→ℕ)
set_option quotPrecheck false
local notation "fields" => (i:ℕ)→ Config G (C.side i p)→Poly (H i)
local notation "β" => C.path.rep N p
variable {F F₀ F₁:(i:ℕ)→ Config G (C.side i p)→Poly (H i)}

omit [(i:ℕ)→Fintype (V i)] in
theorem consistent (hb:n ≤ b) (hm:m ≤ N)
    (run:Replay (H:=H) A s hb m F N) (lo:Replay (H:=H) A s hb m F₀ N)
    (up:Replay (H:=H) A s hb m F₁ N) (h₀:Integrable (F₀ m) (prior G _))
    (h₁:Integrable (F₁ m) (prior G _)) (z:ℂ)
    (head:F m=fun U=>blend (F₀ m U) (F₁ m U) z)
    {i} (bi:b ≤ i) (im:i ≤ m) : F i=fun U=>blend (F₀ i U) (F₁ i U) z := by
  induction im using Nat.decreasingInduction with
  | self=>exact head
  | of_succ j jm ih=>
    obtain ⟨hx,ex⟩:=run.downhill j bi jm
    obtain ⟨hl,el⟩:=lo.downhill j bi jm
    obtain ⟨hr,er⟩:=up.downhill j bi jm
    have bv:=bi.trans j.le_succ
    have integr₀:=lo.live A s hb h₀ hm bv jm
    have integr₁:=up.live A s hb h₁ hm bv jm
    rw [ex,el,er]
    funext U
    unfold downdraft
    rw [ih bv]
    rw [WilsonAllDateHarvestPropagation.measured _ _ (C.path.levels.transition_mass ..) integr₀ integr₁]
    dsimp only
    simp only [blend_eq,linear,map_add,map_smul]

variable (I:∀ i:ℕ,V i→Body) (h:C.Makes) {D:Address.Rail C} (storage:Storage C D)
variable {q f:ℕ→ℝ} {T:Pens C p W}
local notation "board" => fun i (im:i ≤ m) (mn:m ≤ N) (F:Config G (C.side i p)→Poly (H i)) (e:ℝ) =>
  MenuBoard (β i) (imprint h A I T i (im.trans mn)) F (A.supportX i)
    (fun _:V i=>west C q f k i) e 1
local notation "expo" => fun i:ℕ=>if i=m then (C.path.levels.budget i).supportExponent-4
  else (C.path.levels.budget i).supportExponent

include storage in
/-- Choose the full stripped and amplified paths by the original license chain;
no income is spent separately at an intermediate date. -/
theorem original (hb:n ≤ b) (bm:b ≤ m) (mn:m ≤ N)
    (purse:Purse C f q b m d k) (route:Toured A H hb m f k)
    (lamp:Lantern s h (p:=p) (b:=b) (D:=D) m N q T)
    (run:Replay (H:=H) A s hb m F N) (rank:∀i,s i ≤ d) (prep:PreparedA A I b m hb)
    (cap:∀i:V b,Cap (s (A.labelY b i)+2) (I b i) 1)
    {e:ℝ} (width:(C.path.levels.budget m).supportExponent-4 ≤ e)
    {X Y:Config G (C.side m p)→Poly (H m)}
    (base:board m le_rfl mn X e) (high:board m le_rfl mn Y e)
    (δ:ℝ) (hδ:0 ≤ δ) (small:δ ≤ 1) (hm:F m=fun U=>blend (X U) (Y U) (δ:ℂ))
    (three:∀i,b ≤ i→i ≤ m→WilsonAllDateHarvestAffine.Three (H i)) :
    ∃ L:fields, Replay (H:=H) A s hb m L N ∧ L m=X ∧
      ∀i, b ≤ i→∀ im:i ≤ m,
      ∃ (B:Ledger (β i) (imprint h A I T i (im.trans mn)) (L i)
           (A.supportX i) (fun _:V i=>west C q f k i) (expo i))
        (Z:Ledger (β i) (imprint h A I T i (im.trans mn)) (F i)
           (A.supportX i) (fun _:V i=>west C q f k i) (expo i)),
        Towed (fun _:V i=>west C q f k i) id (fun v U=>Z.H v U-B.H v U)
          (β i).p.B (expo i) (2*δ) ∧
        Towed (fun _:V i=>west C q f k i) Prod.fst (fun v U=>Z.K v U-B.K v U)
          (β i).p.B (expo i) (2*δ) := by
  let ticket (j) (bj:b ≤ j) (jm:j < m) := (run.downhill j bj jm).choose
  obtain ⟨L,replayL,hL⟩:=reels_write A s hb bm (H:=H) ticket X N
  obtain ⟨U,replayU,hU⟩:=reels_write A s hb bm (H:=H) ticket Y N
  have low:=session (H:=H) A s I h storage hb mn T purse route lamp replayL rank prep cap width (hL.symm ▸ base)
  have high':=session (H:=H) A s I h storage hb mn T purse route lamp replayU rank prep cap width (hU.symm ▸ high)
  refine ⟨L,replayL,hL,?_⟩
  intro j bj jm
  have eq:=consistent A H s hb mn run replayL replayU (hL.symm ▸ base.cleared)
    (hU.symm ▸ high.cleared) (δ:ℂ) (by rw [hL,hU]; exact hm) bj jm
  rw [eq]
  exact output (three j bj jm) (low j bj jm) (high' j bj jm) δ hδ small

end YM.Integration.WilsonAllDateHarvestReplay
