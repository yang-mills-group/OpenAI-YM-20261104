import YM.Qlocal.Switch

/-!
Extract the actual coefficient functions on a fixed complete **log** (regular) or
forced label. We freely specialize each incoming atomic input to an abstract nilpotent
monomial, and to a different tag algebra. In particular setting an old error variable to
include an extra η works. The costs in this file are on the *coefficient*, before
multiplying back those prices. Removing the markers and summing the quiet branch here
isn't a new unmarked law. This is not the formal conditional Fk
bank -- it's a readout on the genuine precursor, whose high-order budgets use the
purchased Angular prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ₀ : Chi}


open Function Filter Lattice RG RG.Patch Pressure Ovens
open Mallow Motion Progress.DirectedRecipe Refrain Song
open Palette Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas Switch

variable {J : Type} [Fintype ι] (M : ι→Lotus.Leaf R) (D : Ω→ι→Lotus.Leaf R)

namespace UniformPays
variable {A:Activities G c} {p:BudgetPoint} {K:WayK Ω ι G c} (h:UniformPays A p K b a)
-- include quiet (eventually remove it from cost)
abbrev amount (K:WayK Ω ι G c) (x : Ω)(i:ℕ) (U:Config G c)(T:Finset ι) := Switch.jet (fun t s=>K x t s i U) T
include h

lemma quiet (x:Ω) (i:ℕ) (U:Config G c) : amount K x i U ∅= A.K i U:= by
   have hp:= (h.project x).bought; obtain ⟨g,hg,hV⟩:=hp
   exact Eq.trans ((hg i).atZero _ ∅ U) (congr_fun (congr_fun (h.term x ∅) i) U)

lemma keeps (τ:ι→ Support c)
    (hw:∀ x i w,w∈τ i→ Hush i w (fun j=>(A.forced j).support) (K x)) :
    ∃ v:ℕ× Finset ι →ℝ, Ac.Hit (fun i:ℕ×Finset ι=> (A.forced i.1).support) p.B v a b ∧
    ∀ (i : ℕ) (q:Finset ι), 0≤ v (i,q) ∧ ∀ x,
       let f (U : Config G c) := amount K x i U q; let a₀:= A.forced i
       UsesFinal p.threshold a₀.support f∧ Measurable f ∧ GaugeInvariant f ∧
       (∀ U,‖f U‖ ≤ v (i,q) ∧ (f U≠0→ a₀.eligible p.threshold U)) ∧
       ∀ k ∈q, (τ k ⊆ a₀.support ∨ f=0):= by
   obtain ⟨s,hS,H⟩:= h.credit
   choose u hu hu' hY using hS
   refine ⟨fun i=>u i.1 i.2,?_,fun i q=>?_⟩ -- syntax
   · intro w; refine budget_rows _ _ ?_ (H w); intro i; refine budget_finite (fun j'=> ?_) ?_
     · dsimp only; split; next h=> exact mul_nonneg (hu ..) (Real.exp_nonneg _)
       next=> rfl
     by_cases h:w∈(A.forced i).support
     · dsimp only; simp_rw [if_pos h]; rw [← sum_mul]
       exact mul_le_mul_of_nonneg_right (hu' i) (Real.exp_nonneg _)
     simp [h]
   refine ⟨hu i q,fun x=>?_⟩; intro v F; obtain ⟨L,H,hm,hU⟩:= (h.project x).rear i q
   refine ⟨L,H,hm,fun U=> ⟨?_,hU U⟩,fun k hk=> ?_⟩
   · obtain ⟨g,h,hv⟩:= hY i (x,U); unfold v amount; rw [h.exact]; exact hv 0 ⟨le_rfl,zero_le_one⟩ q
   by_cases he : τ k ⊆ F.support; exact Or.inl he
   obtain ⟨w,hp,hW⟩:= Finset.not_subset.mp he; right; funext U
   obtain ⟨v,hv,-⟩:= hY i (x,U); exact Switch.jet_erase hv (fun t _ p=> congr_fun (hw x k w hp i t p hW) _) _ hk
end UniformPays


/- Table (later anchors with support nonempty) uses empty tag only with empty payment.
   `Matches` passes straight to the native scalarization; retaining the slot
   names en route allows revaluation and deletion. -/
structure Spectrum (Ω ι : Type) (G : Gauge) (c : Side) (J : Type) where
   tag : J → Finset ι
   region : J → Support c
   total : J → Prop
   raw : Ω → J → Config G c→ℝ

namespace Spectrum
variable (V:Spectrum Ω ι G c J) (p:BudgetPoint)

def paint (x:Ω)(i:J) (U:Config G c):ℝ:= if V.total i then V.raw x i U else masked p.threshold (V.region i) (V.raw x i) U

structure Reads (L: Ω → J → Config G c → Ways ι) : Prop where
   quiet i : V.tag i = ∅ → ∀ x, V.raw x i = 0
   constant i (ht:V.total i) x U : V.raw x i U = V.raw x i 1
   costumes x i U : Switch.jet (L x i U) = Switch.bench (V.tag i) (V.paint p x i U)

structure Costs (z:ι→Support c) (a e : ℝ):Prop where
   owned i k : k∈ V.tag i → z k⊆V.region i
   locations i : (V.region i).Nonempty
   rent : UniformRooted V.region V.raw p a e

open Marker
variable {α:Type} [DecidableEq α] (B:Marker.Census α) (Z:ι→Poly B)
def polled (x:Ω)(i:J)(U:Config G c): Poly B:= ((↑(V.paint p x i U):ℂ)) • ∏ k∈V.tag i,Z k

def gross (x:Ω)(U:Config G c):Poly B:= ∑' i,V.polled p B Z x i U

lemma service {L: Ω → J → Config G c → Ways ι} (hr : Reads V p L) (x:Ω)(i:J)(U:Config G c):
   V.polled p B Z x i U= sound Z (L x i U):= by
   unfold sound polled; rw [hr.costumes, mapBench]
end Spectrum

namespace Primitive
open Stowe Canyon Marker Ink
variable (Y:Cash W β μ L Q o C T R) (χ:Chi)
variable {M D} (h:Roster M D) (γ:ℝ) (p:BudgetPoint)
    (g:ι→ℝ) (F:Forest S.ratio) (D':Match.Alliance Y Y 1 0)
local notation "cL"=> Cl M Y
local notation "Xz"=> h.castLabel Y
local notation "H'"=> origins M Y
local notation "θ"=>Stowe.recordSet M Y
local notation "ℌ"=> Earnings Y χ h γ p g D'
set_option quotPrecheck false
local notation "A0"=> (Beam.marquee Y p).read (plusone Y D' χ γ)
local notation "K₀"=> fun x=> shoot (D x) Y χ g Y D'
local notation "L₀" => (fun x i=> Ink.yielded (D x) g Y (χ:=χ) (h.castLabel Y x i))
variable {Ψ:ℕ→Prop} {v z e' y s : ℝ} (hr : Earnings Y χ h γ p g D' Ψ n z v e' y s a)

-- also include ancestry in registered cut: retain all expanded sites.
local notation "μk" => (Y.supportP ∘ (Palette.sign M S))
def occupies (i : cL) := ∀ k∈θ i, (μk k) ⊆ H' i
noncomputable def valid (i:cL) := (θ i).Nonempty ∧ Yielding M Y (θ i) i ∧ occupies Y i
local notation "Lx"=> valid Y

def table : Spectrum Ω ι G c (Cl M Y) where
   tag i := if valid Y i then θ i else ∅
   region := origins M Y
   total _ := False
   raw := crop Y h g (valid Y) χ
local notation "V'"=> table Y χ h g

include hr
theorem reads : Spectrum.Reads (V') p (L₀):= by
 refine ⟨fun i hi x=> ?_,fun i=> by rintro ⟨ ⟩,fun x i U=>?_⟩ -- vac defined; false constructor
 · change (if valid Y i then θ i else ∅)=∅ at hi
   have hv : ¬valid Y i:= fun he=> he.1.ne_empty ((if_pos he).symm.trans hi)
   exact if_neg hv
 let T₀:=θ i
 have hf:= hr.masking x i; have he:Stowe.recordSet (D x) Y (Xz x i)= T₀:=rfl
 have hp(s:Finset ι) : Yielding (D x) Y s (Xz x i) ↔ Yielding M Y s i:= Iff.rfl
 by_cases hu: valid Y i
 · unfold Spectrum.paint table; simp only [crop,if_false,if_pos hu]; rw [Stowe.code (D x) g Y (θ i) (Xz x i) (hp _|>.2 hu.2.1) hu.1, (modelClick (θ i) _).exact,hf]
 by_cases hl: Yielding M Y (θ i) i ∧ (θ i).Nonempty
 · have hL : Pillow.glass (D x) g χ (Xz x i)=0:= by
     by_contra hℓ; apply hu
     refine ⟨hl.2,hl.1,fun k hk=>?_⟩
     unfold Function.comp; rw [← h.marks x]; exact Stripes.picture (D x) g Y (Xz x i) hℓ _ hk
   change _=masked p.threshold (origins M Y i) _ at hf; unfold entry at hf; rw [hL] at hf
   have hm : masked p.threshold (origins M Y i) (0:Config G c→ℝ) U=0:= by simp [masked]
   have hx:= (congr_fun hf U).trans hm
   unfold Spectrum.paint table; simp only [crop,if_false,if_neg hu,hm]; rw [Stowe.code (D x) g Y (θ i) (Xz x i) ((hp _).2 hl.1) hl.2,(modelClick (θ i) _).exact,hx]; ext; simp [Switch.bench]
 unfold Spectrum.paint table; simp only [crop,if_false,if_neg hu]; ext s; rw [Stowe.posted_jet]; let s' := (θ i); have hV : ¬ (Yielding (D x) Y s (Xz x i) ∧ s.Nonempty):= fun ⟨hx,ht⟩=> hl (((hp s).1 hx).1.symm ▸ ⟨(hp s).1 hx,ht⟩) -- dependency
 rw [if_neg hV]; simp [masked,Switch.bench]


theorem rental : Spectrum.Costs (V') p μk a s:= by
   refine ⟨?_,?_,?_⟩
   · intro i k h'; change k∈if _ then _ else (∅:Finset ι) at h'; split at h'
     next hv=> exact hv.2.2 k h'
     next=> simp at h'
   · intro i; exact Finset.Nonempty.mono (subset_biUnion_of_mem (Pledge.raised M Y ∘ i.2) (Finset.mem_univ none)) (i.2 none).1.2.1
   obtain ⟨b,hb,hB⟩:= hr.log_all.majorize; refine ⟨b,fun i=> ⟨(hb i).1,fun x=>?_⟩,hB⟩; by_cases h:valid Y i
   · simp only [table,crop,if_pos h]; exact (hb i|>.2 x)
   simp only [table,crop,if_neg h]; exact ⟨CouplingShape.reg_const _, fun _ _=> sup_le (CouplingShape.sup_const _) (abs_zero.trans_le (hb i|>.1))⟩

lemma payment (hh:p.threshold=Pressure.temp β)(ha:0≤a) :
    ∃ f:cL→ℝ, Summable f ∧ ∀ x i,Paid (fun U=> Ink.yielded (D x) g Y (χ:=χ) (Xz x i) U) (f i):=by
    obtain ⟨b,hb,hB⟩:= hr.log_all.majorize; refine ⟨b,?_,?_⟩
    · refine (Push.AbsoluteSums.Product.everyone_ne _ _ (fun i=> (hb i).1) (fun i _ => (rental Y χ h γ p g D' hr|>.locations i: (origins M Y i).Nonempty)) hB).2.1.of_nonneg_of_le (fun i=> (hb i).1) (fun i=>le_mul_of_one_le_right (hb i|>.1) (Real.one_le_exp (mul_nonneg ha (by positivity))))
    intro x i
    let z':= Xz x i
    have hp : ∀ j ∈origins (D x) Y z',p.supBounds j (origins (D x) Y z') (glass (D x) g χ z') (b i):= (hb i|>.2 x).2
    -- `Ink.backed` need threshold_eq p (unused, can inline or pass); apply.
    have hf:= Ink.backed (D x) g Y z' p hh hp (hr.masking x i)
    by_cases hv:Season.allot z'=0; swap
    · refine hf.congr (fun U k hk=>?_); change _=(fun _=>_); exact funext fun p=> (if_pos hv).symm
    refine (Paid.weaken paidZero (hb i|>.1)).congr (fun U k hk=>?_); ext i'; exact (if_neg (not_not.mpr hv)).symm

end Primitive
end YM.Qlocal
