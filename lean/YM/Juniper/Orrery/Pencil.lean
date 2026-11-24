import YM.Juniper.Orrery.Distant
/-!
 # Periodic formal E template (for the verified regrouping at *any* cutoff)

 Dock: exact projections on T (not the Phi chart). Includes name, site, support
 and values globally. From this derive needed layout and membership and
 alignments -- no required derivative correspondence; we derive that of the
 FORECAST reset from the common clover germ and path definitions. Don't
 date the physical coupling from this template!
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Slide
open Progress.DirectedRecipe UVExtension Height StressFlux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c C:Side} {k:ℕ} {ρ:ℝ}
abbrev Margin (B:BudgetPoint)(c:Side):= 50*(1+B.B) ≤ c.val
section lifting
variable {W X:Type*}
variable (hC:C.val=c.val*k) (x:Site C)
local notation "h"=> Deck.divides hC
local notation "F"=> (Macrame.normal h hC)
local notation "H"=> (Macrame.splitter (Deck.divides hC))
structure Leaves (p:W→X) (C':W→RegularAddress C)(v:W→ Config G C→ℝ) (c':X→RegularAddress c)(w:X→ Config G c→ℝ)
     (K:Finset W)(Q:Finset X):Prop where
  root (i:W) : i∈K→ p i∈ Q ∧ H (C' i).site=(c' (p i)).site
  stable (i:W) (hi:i∈K) : (c' (p i)).support = (C' i).support.image H
  truer (i:W) (hi:i∈K) (V:Config G c): v i ((F).links V)=w (p i) V
  serves (i:X)(x:Site C) : i∈Q → H x=(c' i).site → ∃ j, j∈K∧ p j=i∧(C' j).site=x
  uniqueness (i j:W) : i∈K → j∈K → (C' j).site=(C' i).site → p i=p j → i=j
variable (V:Curtain G c) (T:Curtain G C)
def LinkedC : Prop := ∃ p:ℕ→ℕ, Leaves hC p T.book.reg T.stamp.logRead V.book.reg V.stamp.logRead T.sequence V.sequence
structure Model (G:Gauge)(B:BudgetPoint)(H':ℝ) where
   frames (n:Side): Flare.Curtain G n
   dear (n:Side)(ht:Margin B n) : Curtain.TidyC (frames n) B B.B H'
   edges (c C:Side)(k:ℕ)(h' : C.val=c.val*k)(hp:Margin B c): Orrery.LinkedC h' (frames c) (frames C)
-- Tidy asks only pre-E. Special marched at top N need not cast into this form.
variable (B:BudgetPoint) {u : ℕ→ℕ} (L:Leaves hC u T.book.reg T.stamp.logRead V.book.reg V.stamp.logRead T.sequence V.sequence)
      (hv:Curtain.TidyC V B B.B ρ)(ht:Curtain.TidyC T B B.B ρ)(hw:Margin B c)(hG:G.Simple)
local notation "O"=> T.book.reg
local notation "K"=> V.book.reg
local notation "TV"=> T.stamp.logRead
local notation "VT"=> V.stamp.logRead
local notation "U"=> (T.book.read T.stamp)
local notation "V'"=> V.book.read V.stamp
section sums
variable {Y:Type*} [AddCommMonoid Y] {f:ℕ→Y}{g:ℕ→Y}
include L
lemma bills (h' : ∀ i∈T.billed x, f i=g (u i)) : (∑ i∈T.billed x,f i) = ∑ i∈V.billed (H x),g i:= by
    have hq {i} (hi:i∈T.billed x):= mem_filter.mp hi; have hz {i} (hi:i∈V.billed (H x)):=mem_filter.mp hi
    apply Finset.sum_bij (fun i (_ : i∈T.billed x)=> u i) (fun i hi=> Finset.mem_filter.mpr (let t:= L.root i (hq hi).1; ⟨t.1,t.2.symm.trans (congr_arg _ (hq hi).2)⟩)) (fun i hi j hj=> L.uniqueness i j (hq hi|>.1) (hq hj|>.1) ((hq hj|>.2).trans (hq hi|>.2).symm)) _ h'
    intro i hi; obtain ⟨j,hj,hh,hV⟩:= L.serves i x (hz hi|>.1) (hz hi|>.2.symm); exact ⟨j,Finset.mem_filter.mpr ⟨hj,hV⟩,hh⟩
lemma root_cost (W':Config G c) : T.root x ((F).links W')= V.root (H x) W':= by rw [Curtain.amount,Curtain.amount]; exact bills hC x V T L fun i hi=> L.truer i (mem_filter.mp hi|>.1) _
end sums
include L ht hv hG
noncomputable def riseD (Z: c.val ∣ C.val) : Directions G c →L[ℝ] Directions G C := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (R:=ℝ) ((Macrame.splitter Z) i.1,i.2)) -- binder Z macro conflict
local notation "g'"=> riseD (G:=G) (Deck.divides hC)
omit hv in
lemma migrant (i:ℕ)(hi:i∈T.sequence) (a b:Directions G c): logHessian (TV i) (g' a) (g' b) = logHessian (VT (u i)) a b:= by
   let f:=TV i; have hf : B.Regular (O i).support f:= (ht.income.choose_spec.2 i).1; have hb (a:Directions G c): f (increment 1 (g' a)) =((V').E (u i)) (increment 1 a) := L.truer i hi (increment 1 a) -- broken notation V'.
   have hg : (VerifiedReset.germ (TV i)) ∘ (g')=VerifiedReset.germ (VT (u i)):= funext hb
   have hh:= (Work.F03.hessian_comp (g'|>.map_zero) (VerifiedReset.germ_diff hf) (g'|>.contDiff.contDiffAt) (VerifiedReset.flat_critical hG hf)).2 a b; unfold f at hh; rw [hg,ContinuousLinearMap.fderiv] at hh; exact hh.symm

omit L ht hv hG x
include hC hw in
lemma wider : Margin B C:= Nat.le_trans hw (Nat.le_of_dvd C.property (Deck.divides hC))

include L ht hv hw hG
lemma ink_delta (i:ℕ)(hi:i∈T.sequence) : VerifiedReset.projection (O i) (TV i) = VerifiedReset.projection (K (u i)) (VT (u i)):=by
   let j:=u i; let k:= (T.book.reg i).site; let y:= (H k); have hf:= (L.root i hi); let S: RegularAddress c:= K (u i)
   have hL (x) (hx:x∈(O i).support) : separation k x ≤ B.B:= (neighbors_mem ..).mp (ht.frames i hi hx)
   have hz : k=(T.book.reg i).site:= rfl
   have hg : y=S.site:= hf.2
   have hT := wider hC B hw; unfold Margin at hw hT
   have h' {n:Side}(t:RegularAddress n)(hu:Margin B n)(ht: ShortF B.B t): Nonwrapping (VerifiedReset.expand t) t.site:= by
      unfold Margin at hu; apply (Cinch.momentumP (by omega)).2; intro x hx; have hk := (neighbors_mem ..).mp (ht hx); rw [separation_comm] at hk; omega
   funext a b; rw [VerifiedReset.projection,VerifiedReset.projection,if_pos (h' _ hT (ht.frames i hi)),if_pos (h' _ hw (hv.frames (u i) hf.1))]
   have hJ (a:LinearJet G) : Agrees (O i).support (a.field k) (g' (a.field S.site)) := by
      intro v hv _; change a.field k v=a.field _ (H v.1,v.2); unfold LinearJet.field; dsimp only; congr 1; refine Finset.sum_congr rfl fun j hj=>?_ ; unfold VerifiedReset.coord; have hh:=Lattice.separation_comm k v.1; have hp:2*separation k v.1< c.val:= by have hh:= hL _ hv; omega
      rw [Deck.starsL hC k v.1 hp]; exact congr_arg (fun s:Site c=> (↑(lift (H v.1-s) j):ℝ) • a.slope v.2 j) hg
   exact (VerifiedReset.hessian_agrees hG (ht.income.choose_spec.2 i|>.1) (hJ (wedge a (VerifiedReset.spike G))) (hJ (wedge b (VerifiedReset.spike G)))).trans (migrant hC V T B L ht hG i hi ..)

open Averaging
local notation "x*"=> Averaging.axes01
omit L hC hw hG ht hv
include B in
private lemma delta_root {n: Side} (T:Curtain G n) : delta (T.book.read T.stamp)=∑ i∈T.billed (0:Site n),VerifiedReset.projection (T.book.reg i) (T.stamp.logRead i) x* x*:= by
    unfold Averaging.delta Averaging.total; let a:= T.billed (0:Site n); rw [tsum_eq_sum (s:=a) ?_]; swap
    · intro i hi; unfold censusAt; change (if (T.book.reg i).site=0 then projection (T.book.reg i) (T.stamp.logRead i) _ _ else _)=_
      split; next hz=>
        have hx:= VerifiedReset.projection_sub (T.book.reg i) (p:=B) (show B.Regular (T.book.reg i).support (0:Config G n→ℝ) from unspent ..) (show B.Regular (T.book.reg i).support (0:Config G n→ℝ) from unspent ..) x* x*; rw [sub_self,sub_self] at hx; rw [not_ne_iff.mp (mt (T.truncation i) (fun he=> hi (mem_filter.mpr ⟨he,hz⟩)))]; exact hx
      rfl
    exact Finset.sum_congr rfl fun i hi=> if_pos (mem_filter.mp hi).2
include L hC hw ht hv hG in
lemma tint : delta (U) = delta (V'):= by
    let f (i:ℕ):=projection (T.book.reg i) (T.stamp.logRead i) x* x*; let f' (i:ℕ) := projection (V.book.reg i) (V.stamp.logRead i) x* x*; have hp:(∑ i∈T.billed (0:Site C),f i)= ∑ i∈V.billed (H 0),f' i:= bills hC 0 V T L (fun i hi=> congr_arg (fun t:_=>t x* x*) (ink_delta hC V T B L hv ht hw hG i (mem_filter.mp hi|>.1))); rw [map_zero] at hp; exact (delta_root B T).trans (hp.trans (delta_root B V).symm)
end lifting
end YM.Juniper.Orrery
