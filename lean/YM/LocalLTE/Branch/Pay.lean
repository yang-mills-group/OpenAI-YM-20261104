import YM.LocalLTE.Furnace.Feed
/-! Linearity of tracker in split groups at pinned Ledger. Extend labels once.Widen prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Magnet
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Quotes Residual WilsonStartup Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Meadow Ovens.Pipes Rack
variable {G : Gauge} {n : Side} {X : Listing G n} {p : BudgetPoint} {R:PathData G} {c:Clip} {σ C Λ u v Z : ℝ}{H f g : ℕ→ Config G n→ℝ}
def seed (f : ℕ→ Config G n→ℝ): Source G n:= ⟨f,0⟩
lemma promoted (h:Budget p X.reg f Z):Projects (X.read (seed f)) p Z:= by
  obtain ⟨k,h,hk⟩:=h; exact ⟨fun i=>(hk i).1, k,fun i=>(hk i).2,Quotes.segment _ (fun i=>(hk i).2.1) h⟩
-- smooth reg for pure projection or difference doesn't require moves
variable (hG:G.Simple) (hr:R.Bounds c σ C Λ) (hc:Decent c p) (hw:Width p c σ)
variable (h: Budget p X.reg f Z)
variable {a v' : ℝ} (ht: Budget p X.reg g u) (hz: H=f-g)
include hG h ht
lemma detects : Averaging.delta (X.read ((seed (f-g))))= delta (X.read (seed f))-delta (X.read (seed g)):=by
  have he:= promoted h; have hg:= promoted ht; unfold Averaging.delta Averaging.total
  rw [← (he.seriesAt hG ..).tsum_sub (hg.seriesAt hG ..)]; apply tsum_congr; intro i; unfold censusAt; dsimp only [Listing.read]; split
  · exact projection_sub _ (he.regular i) (hg.regular i) ..
  ring
-- ground activated widened calls post-kinematic

def advanced (X : Listing G n) (R:PathData G) (c:Clip) (p:BudgetPoint) (f:ℕ→ Config G n→ℝ) (α:ℝ) := stuff (upE (shelves X R p)) (branch X R c p (seed f) α|>.regular)
include hG
lemma branches (p' : ℝ) (R : PathData G) (c:Clip): advanced X R c p f p'-advanced X R c p g p'=advanced X R c p (f-g) 0:= by
  have he:= promoted h; have hg:= promoted ht; have hx:= detects hG h ht; let q:= upE (shelves X R p)
  have hh (i:ℕ):(branch X R c p (seed f) p'|>.regular i) - (branch X R c p (seed g) p'|>.regular i)=(branch X R c p (seed (f-g)) 0 |>.regular i):= by
    have h: p.Regular _ _:= he.regular i
    unfold branch fill; rw [hx]; exact archive_sub he.regular hg.regular _ p' _ _ _ -- issue implicit a & b
  ext i y; unfold advanced; by_cases hp : i∈Set.range q
  · obtain ⟨k,rfl⟩:=hp; unfold q; rw [Pi.sub_apply,stuffed,stuffed,stuffed]; exact congr_fun (hh k) y
  rw [Pi.sub_apply, blank _ _ hp,blank _ _ hp,blank _ _ hp, sub_zero]
omit ht
-- standalone RegularFamily of each projected field. old alpha=0 when tracking. adapt
-- existing Local proof. Include support all. (not claiming hard fields from seed obey Fits.)
include hr hc
private lemma regular (hn : 20<n.val)(α:ℝ): let F := branch X R c p (seed f) α
    ((shelves X R p).pours F).RegularFamily p:= by
  let D := Averaging.delta (X.read (seed f)); have hp:= promoted h; let F:= archive X R c (seed f) α D; let U:=incoming X R p
  have h₁ (i:EKey n): p.Regular (U i).support (F i)∧F i 1=0:=by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact ⟨rebate_regular _ (hp.regular i),rebate_one ..⟩
    · exact ⟨z.regular (d.fresh_regular R c _ hc (factor*D)),show d.fresh R c 0 _ (pull _ _ 1)=0 by rw [pull_one_field,Low.fresh_one]⟩
    exact ⟨z.regular (d.fresh_regular R 0 hr p (factor*α) (factor*D)),show d.fresh R 0 _ _ (pull _ _ 1)=0 by rw [pull_one_field,High.fresh_one]⟩
  have h₂ (i:EKey n) (he:Nonwrapping (U i).support (U i).site):∀ a b, IsAffineDirection (U i).site a→ IsAffineDirection (U i).site b→ logHessian (F i) a b=0:= by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact rebate_vanish (X.reg i) hG (hp.regular i) he hn
    · apply affine_zero (h₁ _).1
      intro u; exact (z.hessian hG (d.fresh_regular R c 0 hc _) he (by omega) u u).trans (d.fresh_vanish R c 0 hG hc (z.unwrapped he) hn _ _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩))
    apply affine_zero (h₁ _).1
    intro u; exact (z.hessian hG (d.fresh_regular R _ hr p _ _) he (by omega) u u).trans (d.fresh_vanish R 0 hG hr p _ _ _ _)
  exact ⟨fun i=> (h₁ _).1,fun i=> (h₁ _).2,fun i=>h₂ _⟩

def traceE (G:Gauge) (n:Side) (f:ℕ→ Config G n→ℝ) := (drawer G n).pours ⟨f,0,0⟩
include hw
lemma receives (hn : 20<n.val) (α:ℝ) :
    (traceE G n (advanced X R c p f α)).RegularFamily p ∧ (traceE G n (advanced X R c p f α)).EBound p (regularNeed G p c σ C α Z) := by
  have hp:=promoted h; let Δ:=delta (X.read (seed f))
  have hd:=delta_bound hG hp
  have hr':= regular hG hr hc h hn α
  obtain ⟨v,hv,h'⟩:= h
  obtain ⟨he,-⟩:= Local.quote_family (G:=G) hr hc hw α Δ (v:=Magnet.seed f) (fun i=> (h' i).2) hv hd
  let Y:= shelves X R p; let d:= branch X R c p (seed f) α
  have hx : (Y.pours d).EBound p _:=⟨_,fun i => Local.quote_regular hG hr hc α Δ (u:=v) (fun i=> (h' i).2) (fun i=> (h' i).1) (numbering (EKey n) i),fun x => Cost.equiv (numbering _) (he x)⟩
  obtain ⟨ha,hB,hC⟩:=(preserves Y d p).regular hr'; exact ⟨⟨ha,hB,hC⟩, (preserves Y d p).Ebound hx⟩
end YM.AnalyticBridge.VerifiedReset.Collection.Magnet
