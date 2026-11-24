import YM.FormalBulk08.Clover.Tank
import YM.FormalBulk08.Dove.Tares

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {X I:Type}{G:Gauge}{K:KernelChoices}{E e R d D m t j l r :ℕ}{o:Loc G 1}{σ η C:ℝ}
section
variable (F:Frame G d)(H:Hol G)(K:KernelChoices)(o:Loc G 1)
-- schedule purely book, no hypothesis on existence of applicant embedded
-- steering uses cover-price positive for j pairs, no link after L

def preGate (D E R j t:ℕ)(σ η:ℝ):ℝ:=if h:d < D ∧4≤j ∧ d+1 ≤ j-2∧ 4≤ t∧ 0<σ ∧ 0<η ∧ η ≤ coverPrice G K j t then (purchase K F H o D E R j t h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2).choose else 0
lemma licensed (h:d<D)(p:4≤j)(he:d+1≤ j-2)(hu:4≤t)(hs:0<σ)(hw:0<η)(hf:η ≤ coverPrice G K j t) : Passage K F o D E R j t σ η (preGate F H K o D E R j t σ η):= by rw [preGate,dif_pos ⟨h,p,he,hu,hs,hw,hf⟩]; exact (purchase K F H o _ _ _ _ _ h p he hu hs hw hf).choose_spec
def tune (D E R j t:ℕ)(σ η:ℝ)(P:Patch)(V:Lodge P):ℝ:= if h:d<D∧4≤j ∧d+1≤ j-2 ∧ 4≤ t∧ 0<σ ∧ 0<η ∧ η ≤coverPrice G K j t∧ preGate F H K o D E R j t σ η ≤ (P.L.val:ℝ) then (licensed F H K o h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 P h.2.2.2.2.2.2.2 V).choose else 0
lemma good_gate (P:Patch)(V:Lodge P)(h:d<D)(p:4≤j)(he:d+1≤ j-2)(hu:4≤t)(hs:0<σ)(hw:0<η)(hf:η≤coverPrice G K j t)(hz:preGate F H K o D E R j t σ η≤ (P.L.val:ℝ)): Lecture K F o D E R j t σ η P V (Elm.tune F H K o D E R j t σ η P V) := by unfold Elm.tune; rw [dif_pos ⟨h,p,he,hu,hs,hw,hf,hz⟩]; exact (licensed F H K o h p he hu hs hw hf P hz V).choose_spec
-- choose width joints (moving to J+1). Same before L

def spruce (G:Gauge) (i:ℕ) := min (shining K G i) (min (coverPrice G K i i) (coverPrice G K (i+1) i))
lemma spruce_pos (G:Gauge)(i):0<spruce K G i:= lt_min (shining_pos K G i) (lt_min (pricePlus G K i i) (pricePlus G K (i+1) i))
lemma spruce_mod (G:Gauge)(i):spruce K G i ≤ shining K G i:= min_le_left ..
lemma spruce_axis (G:Gauge)(h:t≤j)(he:j≤t+1) : spruce K G t≤coverPrice G K j t:=by
    cases (show j=t ∨ j=t+1 from by omega) with
    | inl e=>rw [e]; exact (min_le_right ..).trans (min_le_left ..)
    | inr e=>rw [e]; exact (min_le_right ..).trans (min_le_right ..)
end
variable {W:Lab G K X}

def amounts (F: Frame G d)(H:Hol G)(W:Lab G K X)(o:Loc G 1)(D E R:ℕ)(i:Leaf W.scrolls):=Elm.tune F H K o D E R (W.upper i) (W.lower i) (W.windowU i) (W.windowD i) (W.pat i) (W.wood i.a i.b)
structure Quota (F:Frame G d)(H:Hol G)(W: Lab G K X)(o:Loc G 1)(D E R:ℕ): Prop where
    horizon: d+1≤D
    level: ∀ i,d+1≤W.upper i-2
    width: ∀ i,W.windowD i ≤coverPrice G K (W.upper i) (W.lower i)
    gate: ∀ i:Leaf W.scrolls, preGate F H K o D E R (W.upper i) (W.lower i) (W.windowU i) (W.windowD i) ≤ wideA i
    running: Soft (chron W.scrolls) (amounts F H W o D E R)

variable {F:Frame G d}{H:Hol G}{ρ: ChartRatio G}
lemma Quota.shift (h:Quota F H W o D E R)(f:I→X): Quota F H (W.wturn f) o D E R:= by
    let g:= turnLeaf W.scrolls f; exact ⟨h.horizon,fun i=>h.level (g i),fun i=> h.width (g i),fun i=> h.gate (g i), Soft.reach h.running g⟩
lemma Quota.supply (h:Quota F H W o D E R)(u:W.Use ρ E)(i:Leaf W.scrolls): Lecture K F o D E R (W.upper i) (W.lower i) (W.windowU i) (W.windowD i) (W.pat i) (W.wood i.a i.b) (amounts F H W o D E R i):= by have hv:= u.haveJ i; exact good_gate _ _ _ o _ _ h.horizon (by omega) (h.level i) ((W.V i.a).clock.adm _) (u.zero (stageFoot _ i 1)) (u.zero i) (h.width _) (h.gate _)
lemma quota_fits (h:Quota F H W o D E R) (i): d ≤ W.upper i:= by have ht:=h.level i;omega
lemma payroll_from (C: Pin W.scrolls)(h:Quota F H W o D E R)(u:W.Use ρ E)(M:X→ℕ) : Payroll K F o (graded W.liftF (W.trail (C:=C) M)) W.liftU E R D (Dove.tide C) W.stub W.sail (Dove.Turn.rad (1/2)):= by
    let Q:= amounts F H W o D E R; have Hx:=h.running.reach (fun i:Turn C=>i.toLeaf); have ht(i:Turn C):=h.supply u i.toLeaf
    refine ⟨fun i=>u.zero i.toLeaf,fun e he r hr l hl=> ⟨_,Hx,fun i=>?_⟩,fun r he=> ⟨_,Hx,fun i=>(ht i).plus,fun i=>(ht i).pupils r he⟩⟩
    have hh := (ht i).bill (graded W.liftF (W.trail M) i) (W.liftU i) rfl rfl e he r hr l hl
    change Office _ F _ _ _ _ _ _ _ _ _ (Dove.Mulct ((W.V _).S.block _)) _ at hh; rw [Dove.mulct_step] at hh; exact hh
end YM.FormalBulk08.Elm
