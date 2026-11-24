import YM.Juniper.Flare.Permit
/-!
 # Wire up actual output representative y to the *independent forecast’s*
 E code. The forecast at output can use ANY labeling in World.Template subject
 to Kit, not F bartered from actual occupancy. Keep hard actual and make all these
 embeddings explicitly before talking of errors.

 Carved is only the E part of `Progress/DIRECTED_RECIPE/Padding.Readdress`,
 adapt some proofs. Full K residents never relabelled by it, not asserting K
 terms disappear (need the actual K entries for valuations). This supports
 speaking of a model slot and reading all ordinary masks and support obligations
 in its syntactically independent expression rather than extracting anything anew.
 Turns, analyticity, and locality AFTER CUT still to buy.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Stellar Greenbelt UVExtension UVExtension.Tabernacle
open Poll Pond MeasureTheory ProbabilityTheory
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain Ovens Ovens.Pipes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c : Side} {B:BudgetPoint}
section tape
variable {V W X: ℕ → RegularAddress c} {v w x : ℕ→ Config G c → ℝ}
structure Carved (V:ℕ→ RegularAddress c) (v:ℕ→ Config G c→ℝ) (W:ℕ→ RegularAddress c) (w:ℕ→ Config G c→ℝ) where
    θ : ℕ ↪ ℕ
    align (i:ℕ): W (θ i)= V i
    keeps (i:ℕ): w (θ i)=v i
    forget (i:ℕ): i∉ Set.range θ → w i=0
variable (i : Carved V v W w) (j:Carved W w X x)
namespace Carved
def compose : Carved V v X x where
   θ:= i.θ.trans j.θ
   align Z:= (j.align (i.θ Z)).trans (i.align Z)
   keeps Z:= (j.keeps (i.θ Z)).trans (i.keeps Z)
   forget Z h:= by
      by_cases hz: Z∈ Set.range j.θ; · obtain ⟨T,rfl⟩:=hz; rw [j.keeps]; apply i.forget _; rintro ⟨p,rfl⟩; exact h ⟨_,rfl⟩
      exact j.forget Z hz

def refl (V:ℕ→ RegularAddress c) (v:ℕ→ Config G c→ℝ) : Carved V v V v := ⟨Embedding.refl _,fun _=>rfl,fun _=>rfl,fun j hj=> (hj ⟨_, show (Embedding.refl ℕ) j = _ from rfl⟩).elim⟩ -- check metavars
variable (B)
noncomputable def figured (V:ℕ→ RegularAddress c) (v:ℕ→ Config G c→ℝ) (B: BudgetPoint) := fun U=> ∑' i,masked B.threshold (V i).support (v i) U
-- v arg named G wrong
include i
lemma visible : figured V v B=figured W w B:= by
   funext U; apply Eq.symm; apply (Progress.DirectedRecipe.transferred_sum i.θ); · intro j; rw [i.align,i.keeps]
   intro k hg; rw [i.forget _ hg]; simp [masked, Set.indicator]
lemma readdress {A A': Activities G c}(h:A.reg=V)(hw:A.E=v) (hp:A'.reg=W)(hq:A'.E=w): A'.additive B=A.additive B:= by
   have H (V:Activities G c): V.additive B=figured V.reg V.E B:= rfl
   rw [H,H,h,hw,hp,hq]; exact (i.visible B).symm
end Carved
end tape
open Voucher
variable {V W X: Listing G c}{v w:Collection.Source G c}
section nest
local notation "P"=> numbering (ℕ⊕ℕ)
-- arrow of carved through stack actual and Predictor.K (F stack etc)
def stacked (X V W:Listing G c) (v w : Collection.Source G c): Carved W.reg w.logRead (package X V W).reg (stack v (Voucher.void G c) w).logRead where
   θ:= Embedding.trans ⟨Sum.inr,Sum.inr_injective⟩ (P).symm.toEmbedding
   align j:= by change Sum.elim _ W.reg (P ((P).symm (.inr j)))= _; rw [(P).apply_symm_apply]; rfl
   keeps j:= by change Sum.elim _ w.logRead (P ((P).symm (.inr j)))=_; rw [(P).apply_symm_apply]; rfl
   forget j hj:= by change Sum.elim (0:ℕ→ Config G c→ℝ) w.logRead (P j) = _; cases h:P j; next=> rfl
                    next p=> exact (hj ⟨p,show (P).symm (.inr p) = j from ((P).symm_apply_eq).2 h.symm⟩).elim

def rainbows (X:Listing G c)(w v: Collection.Source G c)(B:BudgetPoint)(b:ℕ)(f:Offer G c): Carved X.reg w.logRead (pluck B (lodge X 0 b)).reg (overlay X v b f («P»:=B) w).logRead where
   θ:= Embedding.trans ⟨Sum.inl, Sum.inl_injective⟩ (leanU c).symm.toEmbedding
   align j:= by change Sum.elim X.reg _ (leanU c ((leanU c).symm (.inl j)))= _; rw [Equiv.apply_symm_apply]; rfl
   keeps j:= by change Sum.elim w.logRead _ (leanU c ((leanU c).symm (.inl j)))= _; rw [Equiv.apply_symm_apply]; rfl
   forget j hj:= by
      change Sum.elim w.logRead (choir (0:Offer G c)) (leanU c j)=_
      cases h: leanU c j; next j'=> exact (hj ⟨j', (show (leanU c).symm (Sum.inl j') = j from ((leanU c).symm_apply_eq).2 h.symm)⟩).elim
      next=> simp only [Sum.elim_inr,Voucher.nothing]
end nest
section fill
local notation "G₁"=> numbering (Collection.EKey c)
variable (R:PathData G)(B)(c':Clip)(β γ:ℝ) (f : Carved X.reg v.logRead W.reg w.logRead)
open Residual
-- actual correspondence of PRE and POST subtraction of kinetic & pose. Rebates use only entries not density; covered. For empty-coordinate projection require true local proof (uses all X jets).
include B
private lemma rebate_zero (A: RegularAddress c) : Residual.rebate A (0:Config G c→ℝ)=0:= by
   have he:= (Residual.label_sub A (0:Config G c→ℝ) 0 (0:Config G c→ℝ) B (show B.Regular A.support (0:Config G c→ℝ) from unspent ..) (show B.Regular A.support (0:Config G c→ℝ) from unspent ..)).1; rwa [sub_self,sub_self] at he -- arg order

omit B
def castFuel (f : ℕ ↪ ℕ) (c:Side): EKey c ↪ EKey c := Embedding.sumMap f (Embedding.refl _)
variable {I J:Type}
def Carved.sigma (L:ℕ≃I) (K:ℕ≃J) (t:I↪J) (g:I→RegularAddress c)(u:I → Config G c→ℝ)
    (v:J→RegularAddress c)(w:J → Config G c→ℝ)
    (he:∀ i,v (t i)=g i)(hk:∀ i,w (t i)=u i)(hz : ∀ j,j∉Set.range t→ w j=0): Carved (g ∘ L) (u∘ L) (v∘ K) (w∘ K):= by
    let T:= L.toEmbedding.trans (t.trans K.symm.toEmbedding); have ha i: K (T i)=t (L i):= K.apply_symm_apply _
    refine ⟨T,fun i=> ((congr_arg v (ha i)).trans (he (L i))),fun i=> ((congr_arg w (ha i)).trans (hk (L i))),fun i hi=> hz _ ?_⟩
    rintro ⟨j,h⟩; exact hi ⟨L.symm j,K.injective ((ha (L.symm j)).trans ((congr_arg _ (L.apply_symm_apply j)).trans h))⟩

local notation "ε"=> castFuel f.θ c
include f
include B in
private theorem kestrel_a (i:EKey c) : Collection.incoming W R B (ε i)=Collection.incoming X R B i:= by
    rcases i with i|i; · exact congr_arg enlarges (f.align i)
    rfl
private theorem kestrel_b (i:EKey c) : Collection.archive W R c' w β γ (ε i)=Collection.archive X R c' v β γ i:= by
    cases i with
    | inl i =>
       have hT : ε (Sum.inl i)=Sum.inl (f.θ i):= rfl
       rw [hT]; simp only [Collection.archive,Sum.elim_inl]; rw [f.align, f.keeps]
    | inr j => rw [show ε (.inr j)=Sum.inr j from rfl]; simp only [Collection.archive,Sum.elim_inr]

include B in
private theorem kestrel_c : ∀ i, i∉ Set.range ε → Collection.archive W R c' w β γ i=0:= by
    rintro (i|i) hi
    · have ht : i∉ Set.range f.θ:=by rintro ⟨p,h⟩; exact hi ⟨.inl p,congr_arg Sum.inl h⟩
      change rebate _ (w.logRead i)=_; rw [f.forget i ht,rebate_zero B]
    exact (hi ⟨.inr i,rfl⟩).elim

include B in
def reclosed : Carved (Collection.shelves X R B).reg (Collection.fill X R c' B v β γ).regular (Collection.shelves W R B).reg (Collection.fill W R c' B w β γ).regular :=
    Carved.sigma G₁ G₁ (ε) (Collection.incoming X R B) (archive X R c' v β γ) (Collection.incoming W R B) (archive W R c' w β γ) (kestrel_a B R f) (kestrel_b R c' β γ f) (kestrel_c B R c' β γ f)

end fill
section finishing
open Cinch
variable (P : Pipes G c) (b : Tap G c)(t:Pylon B c)
local notation "F"=> Cinch.badge c

def stitched : Carved P.reg b.regular (adobe P t).reg (flint t 0 b).regular where
   θ:= Embedding.trans ⟨Sum.inl, Sum.inl_injective⟩ (F).symm.toEmbedding
   align j:= by change Sum.elim P.reg _ (F ((F).symm (.inl j)))= _; rw [Equiv.apply_symm_apply]; rfl
   keeps j:= by change Sum.elim b.regular _ (F ((F).symm (.inl j)))= _; rw [Equiv.apply_symm_apply]; rfl
   forget j hj:= by
      change Sum.elim b.regular (Pylon.gap 0) (F j)=_
      cases h: F j; next i=> exact (hj ⟨i,(show (F).symm (.inl i)=j from ((F).symm_apply_eq).2 h.symm)⟩).elim
      next i=> simp [Pylon.gap,twill]
open Rack in
def printable : Carved P.reg b.regular (drawer G c).reg (Rack.widen P b).regular:=
    ⟨upE P,reg_up P,fun i=> Progress.DirectedRecipe.stuffed _ _ i,fun _ h=> Progress.DirectedRecipe.blank _ _ h⟩
end finishing
end YM.Juniper.Flare
