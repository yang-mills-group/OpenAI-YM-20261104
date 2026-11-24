import YM.RG05Readout.Petals.Pollen
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Kernel Dash
local notation "i!"=> Cutoffs
local notation "F"=> f.fuse
local notation "Σ!"=> Palette C d
variable (u: ∀ (_i:Cutoffs), Emblems C d)(M:Cutoffs→Palette C d)

/-! Detector kernels ruling. Gate 
 For any U backbone and tuned capped family deliver budgets on projections
 at ALL higher stencil orders, and coherence on any subfilter. Establish actual
 numerical read limits in the physical detectors as the continuum field v from
 ONE such witness. Supplies all P panels with same physical v, hence readout
 as bounded operator for numerical conduct. -/
variable {L₀:ℕ→YM.Table C.book}{T S:YM.Table C.book}{E:DiffPlan T}{R:Dash.Bin S}(H: Next.Extract.Base C f S L₀ R T E)(hF:UVExt.Slots.StrongBin C R f d)
   {φ: Filter Cutoffs}(hp:φ ≤ f.fuse)
abbrev exactP (C:Family G)(f: Extraction.Order)(P:Trial C){S: YM.Table C.book}(R:Dash.Bin S)(x:Rowe C d): Prop:= (∀ i,(R d).step i (x i)=x i)∧ Reveals C f P x
abbrev Script (U: ∀ (_i:Cutoffs), Emblems C d)(M:Cutoffs→Palette C d) (m:ℕ)(φ: Filter Cutoffs)(S:YM.Table C.book)(p:S.Hierarchy)(v:C.label d): Prop:=∀ j:ℕ,∀ L':Poem C j,Tendsto
    (fun i:Cutoffs=> preamble L' i.1 i.2 (fieldC C m i.1 i.2 d (fastU U M m i) L'.opening)) φ (𝓝 (Poem.passField L' S p.smooth d (S.project d v))) -- F notation conflict
include H
include h hp
lemma forecast {P:Trial C} {x':Rowe C d} {x:C.label d}(hx: exactP C f P R x')(hv:Tendsto x' φ (𝓝 x))(j:Shot C.book): Tendsto (uncurry (Bid.targetB P j)) φ (𝓝 (j.core T (Poem.sanctioned H.kernel.smooth) x)):=by
    have hL:= (arcing ((j.ready H.arrives.born H.arrives.census.integral d).mono_left hp) hv); let B:= (j.core S H.arrives.born (d:=d) x); have hm:= ((on_profile h x' j hx.2 H.center).mono_left hp).add hL; rw [zero_add] at hm; have he:B=j.core T (Poem.sanctioned H.kernel.smooth) x:= Dash.faithful H.clean.sharp j.f (j.record x); rw [← he]; apply Tendsto.congr' _ hm; exact Eventually.of_forall fun i=> by change (targetB P j i.1 i.2 - j.scan _ _ _ _) + _= _; rw [sub_add_cancel];rfl
variable (hU:UniformM f u b D B h)(hM:b ≤ m)(c':ℝ)(hm:∀ᶠ i in f.fuse,size (M i) ≤ c')
variable {w:Worth}{ζ:ℕ→ℕ} (Y:OPE.Package C w ζ D)(Ys:Storage C D)(hG:G.Simple)
variable {I:Type}[Fintype I]{P₀:I→Poem C n} {c:ℝ} (hP:Proctor C f R n d I P₀ c)
include h hU hM c' hm Y Ys hG hF H hp hP
local notation "P!"=> fastU u M m
local notation "Z"=> fun k=> code m k (fastU u M m)
variable {x':Rowe C d} {x:C.label d}(hx: exactP C f (code m k (fastU u M m)) R x')(hX:∀ i, craving (P₀ i) d ≤ k)(hv:Tendsto x' φ (𝓝 x))
include hx hX hv
lemma future (K:ℕ)(hk:k ≤ K): ∃ q : Rowe C d, exactP C f (code m K (fastU u M m)) R q ∧ Tendsto q φ (𝓝 x) :=by -- uM shadow
    let HE:= onboard h u M hU hM c' hm
    obtain ⟨q,ha⟩:=favored h u M hU hM c' hm Y Ys hG H hF hP le_rfl (by simpa using HE) (fun i=> le_trans (hX i) hk)
    have he := pilot_similarity h H hP hx.2 (v:=x') (w:=q) ha.2 hx.1 ha.1 (fun i=> ?_); swap
    · have ht:= (with_pledge h (m:=m) (P₀ i) _ Y hG HE (hX i)).sub (with_pledge h (m:=m) (P₀ i) _ Y hG HE ((hX i).trans hk)); rw [sub_zero] at ht; apply ht.congr'; exact Eventually.of_forall fun _=>by abel
    have hm:= hv.sub (he.mono_left hp); rw [sub_zero] at hm
    exact ⟨q,ha,hm.congr (fun j=> by abel)⟩
lemma audible : Script u M m φ T H.kernel x:=by
   have HE:= onboard h u M hU hM c' hm
   intro j D'; obtain ⟨q,hA,hB⟩:= future h u M H hF hp hU hM c' hm Y Ys hG hP hx hX hv (max k (craving D' d)) (le_max_left ..)
   have hw:= (forecast h H hp hA hB D'.sight).sub ((with_pledge (m:=m) h D' _ Y hG HE (le_max_right k _)).mono_left hp); rw [sub_zero] at hw; rw [Poem.intact (h:=H.kernel.laws.toSymmetric)]; apply hw.congr; intro i; change targetB _ _ _ _-(_-_)=_; rw [sub_sub_cancel]
end YM.RG05Readout.Petals
