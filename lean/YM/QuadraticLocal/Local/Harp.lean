import YM.QuadraticLocal.Local.Primer
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Venue
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open RemainderComparison RemainderComparison.Portal RemainderComparison.WickReps RemainderComparison.Aria.Pose
open AllOrder AllOrder.Catch AllOrder.Wheel AllOrder.Wheel.Ride Further.LogJets AllOrder.Burn Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {L n f:Side}{α:Type*} {V I :Type} [Fintype V][DecidableEq V] {N k r e:ℕ} {a c:ℝ}
open Sunrise Echo Poetry AllOrder.Ink Deck
namespace Harp
variable (v:V)(w:V→ Site f)(X:ℕ→ Roll G V)(Z:∀ i,Finset (X i).Ty)
variable (h:n.val=f.val*k) (p:V→ Site n)(hp:∀ i,w i=(Macrame.splitter (Deck.divides h)) (p i))
set_option quotPrecheck false
local notation "ζ"=> Macrame.splitter (Deck.divides h)
local notation "ν"=> normal (Deck.divides h) h
-- relative to chosen center x in the big state. Need ALL roots locations including attachments.H.Point.Temporal rank.Build.Anchor.Caption
open Pair.Splint
local notation "Φ" p=> Pair.Splint.song v p X Z a N e
local notation "φ" t:max q:max=> Minty.peck v t (X q) (Z q) N
-- reach length ≥ one needs radius comparator. Guardian.Weight less growth.P.Flow.World.Shape.Input.Account
variable (hr:2*r<f.val) (hk:N ≤ r) (hc:∀ i:V,separation (p v) (p i)≤r)
include hp hk hc hr
lemma covers (q:ℕ) : Minty.peck v p (X q) (Z q) N=Minty.peck v w (X q) (Z q) N:= by
 let H:= p v; let h':= Deck.divides h; ext i; let X':=(X q).leg i; unfold Minty.peck; simp only [mem_filter]; refine and_congr_right fun hi=> and_congr_right fun hh=> ?_
 constructor
 · intro h₁ y hy; rw [hp,hp, h₁ y hy, map_add, Macrame.branch ..]
 intro h₂ y hy; let x:= H + wrap n y.1; apply Deck.tiniest h'; · rw [← hp y.2,h₂ y hy]; rw [map_add,Macrame.branch, ← hp]
 change separation (p y.2) x < _
 have hh':separation H x≤ r:= (AllOrder.Ink.Rail.le_window H y).trans (le_trans ?_ hk); swap; · have hl: Ink.meter X'.roots+X'.atom.length≤ N:=hh; refine le_trans (?_:Laurent.size y.1 ≤ Ink.meter X'.roots) ((Nat.le_add_right ..).trans hl); unfold Ink.meter; exact List.le_sum_of_mem (List.mem_map.mpr ⟨y,hy,rfl⟩)
 have hv1: separation (p y.2) H ≤ r:=by rw [separation_comm]; exact hc _
 exact lt_of_le_of_lt ((separation_triangle _ H _).trans (Nat.add_le_add hv1 hh')) (by omega)
lemma spark (A:Config G f)(a:ℝ)(e:ℕ) : Pair.Splint.song v p X Z a N e ((ν).links A)= Pair.Splint.song v w X Z a N e A:= by
 unfold Pair.Splint.song; simp only [Finset.sum_apply]; refine sum_congr rfl fun i _=> ?_; rw [covers v w X Z h p hp hr hk hc]; apply Finset.sum_congr rfl; intro k hk; unfold Trace.offered; rw [Pi.smul_apply,Pi.smul_apply, hp]; unfold Atom.unmasked RG.Slot.atSite; rw [ (ν).expansion]; rfl
omit hp hk hc hr
variable (e N)(t:BudgetPoint)(hs:∀ i≤e,(X i).honest)
local notation "W"=> (neighbors r (p v))
local notation "Ψ"=> (neighbors r (w v))
include hs hk
lemma regular (a:ℝ): t.Regular (neighbors r (p v)) (Pair.Splint.song v p X Z a N e):=by
 refine Meadow.regularA _ (fun i hi=>Meadow.regularA _ (fun j hj=> CouplingShape.reg_scale _ ?_)); let T':=(X i).leg j; have hx:T'.atom.Invariant:= hs i (Nat.le_of_lt_succ (mem_range.mp hi)) j; refine CouplingShape.reg_extend (Derivs.canonical_regular _ (p v) t hx) ?_
 let p₀:Loan:= ⟨T'.r,T'.r,1,by decide,by omega⟩; apply Cafe.plot (p v) p₀ (T'.atom); have ht: T'.length ≤ N:= (mem_filter.mp hj).2.1; exact (Nat.le_add_left ..).trans (ht.trans hk) -- hp `.p` implicit?
local notation "z"=> p v
variable {C:Side}{M:ℕ} (hv:n.val=C.val*M)(T:V→ Site C)(hT:∀ i,T i=(Macrame.splitter (Deck.divides hv)) (p i))
variable (hu:2*r<C.val)(hy:2*(r+1)<n.val)
include h hv hp hr hc hu hT hy
-- Γ exact lens model log.Adv.Ph any mask CPS_S.Security.Owner
lemma correspondence (a:ℝ): Spool.Lending (T v) (w v) (Pair.Splint.song v w X Z a N e) (Pair.Splint.song v T X Z a N e) t r:=by
 constructor; · exact (regular N e v X Z w hk t hs a).sites -- order
 intro V Z' _ _ hZ; let U':=(ν).links V; let U'':=(normal (Deck.divides hv) hv).links Z'; let g:=Pair.Splint.song v p X Z a N e; rw [← spark v w X Z h p hp hr hk hc, ← spark v T X Z hv p hT hu hk hc]; refine (regular N e v X Z p hk t hs a).sites _ _ (Slide.readNear (p v) hy ?_); rw [(ν).expansion,(normal (Deck.divides hv) hv).expansion]; rw [hp,hT] at hZ; exact hZ
end Harp
end YM.QuadraticLocal.Venue
