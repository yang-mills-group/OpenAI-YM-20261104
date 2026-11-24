import YM.Pier.Reserve.Pass
import YM.Pier.Reserve.Native
import YM.FullVolume.Gables.Gates
import YM.RG17.Refresh
/-!
# Actually pay the forced-input feedback distortion through arbitrary corridors

R, its REGULATOR (period,mesh), steps, and gates held fixed: cost a very
specific EDIT of the graph transform at every intermediate level dropping the
**incoming** K component of the marks for the comparison. Both E AND K are
computed as output of every edited step (and detector reset/inversion still
performed at that step); price always in the full norm! Keep local leader
maps also. Use this for the singleton graph-transform *within* a more precise
comparison, not as a matched coupling model or approximating *only with E*.
Absolutely no edit to the geometry, budgets, reference/bare β or the density
of the physical unmarked vacuum is priced here (that's a separate problem).
Explicitly does NOT claim a new history with this projection, that the returned
value at reference leader labels is unchanged or priced thru many transfers in
those coordinates, or that this edit alone is sufficient for cheap scale distortion!
FullVolume Mark/Gables Clubs use `Gram`, here NOT the two point matrix, `flow`
is the numerical single-mark transformation with recalibration. Physical due
terminal reference conversion still required; pert. readouts beyond this file.

Prices at every step in its own gear. No transporting through incompatible
field alignments or phases.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Pier.Mooring
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus Legato Legato.Campaign Legato.Bandage
open YM.MergeProof Matric Matric.Gram
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Guard RG.Shoot Lark Rain Blush Motion Boutique
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (R:Run G) {T:Legato.Campaign R} (W:Pillars R T) (h:G.Simple)
variable {p N d : ℕ}
set_option quotPrecheck false

/- R.stories and canonical column labels are the same as R.family*. Use Run
so that the levels and acclaim gates stay available in the following recurrences. -/
abbrev Grid (m:ℕ) (p d : ℕ) := Gram ((Labels.frames G).level d) (hol G) (attire R.T m p)
    (R.alloy.B.a.params m).columns
abbrev dept (p:ℕ) (d:ℕ) (m:ℕ) := CircleK (A:=R.alloy) (fun i=> attire R.T i p) d m
abbrev books (N p d:ℕ) (m:ℕ) :=
   (W.yields N p).cargo R.b (fun i=> brochure R.T i p R.tuning.receipts)
     (Nat.zero_le _) (R.accepts d) (R.stories d N p) (fun hn=> W.ports d N p hn) m
abbrev stepTo (N p d:ℕ) (m:ℕ)(hm:R.t d ≤ m): dept R p d m := (W.yields N p).tuition h R.b
     R.tuning.receipts (fun i=> brochure R.T i p R.tuning.receipts)
     (Nat.zero_le _) (R.accepts d) m hm

section rung
variable (m:ℕ)(hm:R.t d ≤ m) (hj:m<N)
local notation "P" => (stepTo R W h N p d m hm)
local notation "μ" i => Real.sqrt (R.alloy.B.a.clock.forcedAllowance i)
local notation "β" i => R.alloy.B.a.clock.hatBeta i
local notation "F"=> (Labels.frames G).level d
local notation "s₁"=> (R.alloy.B.a.params (m+1)).columns
local notation "r₁"=> ruby d R.alloy.B.a m
include hj
lemma placement : (books R W N p d m) = (stepTo R W h N p d m hm).flow (books R W N p d (m+1)) ∧
    ∀ x,(R.stories d N p|>.entries m x).x=(P).leanings (books R W N p d (m+1)) ((R.stories d N p|>.entries (m+1) x).x) :=
    (W.yields N p).tallies h R.b R.tuning.receipts _ _ _ _ _ _ _ hj
lemma payment (Q U:Grid R (m+1) p d)(c:ℝ)(hc:0≤c)(hk:InRange (R.family.path) N p m Q U c) :
    Within ((P).flow Q) ((P).flow U) (c/2) ∧
    Costed ((P).leanings Q).toLinearMap ((P).leanings U).toLinearMap (r₁*c) ∧
    r₁*c*s₁ ≤ c/4 := by
   let B := W.yields N p
   let D := B.steps m (Nat.zero_le _) hj
   let ht:= R.accepts d|>.trans (R.alloy.B.a.fits.mono hm)
   let V':=D.castT R.b B.choice ht
   have hx:= Boutique.fair h R.b R.T ht R.tuning.receipts D B.choice
   have ha:= (tickets h R.b D B.choice ht R.tuning.receipts).swing
   have hL:= D.pierTables h R.b B.choice ht R.tuning.receipts
   have hz : stepAllowance F s₁ (Doors.rate ((R.family.path).S.block m)) c = r₁*c := by
       unfold stepAllowance ruby; change _= Doors.rate ((R.family.path).S.block m) * _ * _ * _; ring
   rw [show stepTo R W h N p d m hm=B.five h R.b R.tuning.receipts _ _ _ _ hm hj from
           B.argues h R.b R.tuning.receipts _ _ _ m hm hj]
   have hV:= B.notices (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) hj
   have hW:= B.notices (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) hj.le
   refine ⟨withinStep V' hx hL hV ha Q U hk R.b.clock.room R.b.clock.bank hW hc,?_,?_⟩
   · rw [← hz]; exact indexCost V' hx hL hV ha Q U hk R.b.clock.room R.b.clock.bank hc
   rw [← hz]; exact manageable V' hx R.b.clock.bank hc

lemma ringout (Q:Grid R (m+1) p d) : Within ((P).flow Q) ((P).flow (soft Q)) ((μ (m+1))/2) ∧
    Costed ((P).leanings Q).toLinearMap ((P).leanings (soft Q)).toLinearMap (r₁*μ (m+1)) := by
  obtain ⟨ht,hc,-⟩:= payment R W h m hm hj Q (soft Q) _ (Real.sqrt_nonneg _) (exposes
    ((W.yields N p).notices (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) hj) Q)
  exact ⟨ht,hc⟩

/- Deliberately expose the end of the angular estimate in native price, before
invocation of any cumulative-product distortion. That further product is not
paid here (and there are weight gaps). Even if `μ` isn't spent the precision
of each A-coordinate step is fine enough to be used at every fixed order. -/
lemma payload (Q U : Grid R (m+1) p d)(c:ℝ) (hu:Within Q U c)(hκ:(μ (m+1)) ≤ c) :
    Within ((P).flow Q) ((P).flow (soft U)) c ∧
    Costed ((P).leanings Q).toLinearMap ((P).leanings (soft U)).toLinearMap (r₁*c+r₁*c) ∧
    (r₁*c+r₁*c)*s₁ ≤ c/2 := by
  obtain ⟨he,hT⟩ := ringout R W h m hm hj U
  have hr:= rubies d R.alloy.B.a m
  have hv:= Gram.widen (((P).trail Q U c hu).trans he) (show c/2+(μ (m+1))/2 ≤ c by linarith only [hκ]) (zero_le_one.trans (R.alloy.B.a.params m).columns_ge)
  have hv₁: Costed ((P).leanings Q).toLinearMap ((P).leanings (soft U)).toLinearMap (r₁*c+r₁*c):=
    cost_raise (cost_trans ((P).toward Q U c hu) hT) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hκ hr))
  have hp : InRange (R.family.path) N p m U (soft U) c:= by
    intro i; obtain ⟨a,b,hp,hq⟩:= exposes ((W.yields N p).notices (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) hj) U i
    exact ⟨a,b,hp,hq.trans (mul_le_mul_of_nonneg_right hκ (zero_le_one.trans (R.alloy.B.a.params (m+1)).columns_ge))⟩
  have he : r₁*c*s₁ ≤ c/4:= (payment R W h m hm hj U (soft U) _ hu.1 hp).2.2
  refine ⟨hv,hv₁,?_⟩; rw [add_mul]; linarith only [he]
end rung

/-- No claim of density-preservation on this edit. Exact branch-local numerical
step on regular+forced column graph and leader *after*, artificially, ejecting
just the forced input from the stock marks (not from vacuum!). The recursion
retains the full output stock. At next step again do this to the incoming K, if
above the indicated point. -/
def corridor (N p d e m:ℕ) : Grid R m p d :=
    if q:R.t d ≤ m ∧ m < e then
      (stepTo R W h N p d m q.1).flow (soft (corridor N p d e (m+1)))
    else (books R W N p d m)
termination_by e-m

lemma vacant (e:ℕ)(x:ℝ)(hx:0≤x) : Within (books R W N p d e) (corridor R W h N p d e e) x := by
    rw [corridor,dif_neg (by omega)]
    exact ⟨hx,fun i=> by rw [sub_self,norm_zero]; exact mul_nonneg (mul_nonneg hx
      (zero_le_one.trans (R.alloy.B.a.params e).columns_ge)) (Work.G08.size_nonneg ..)⟩

lemma keep (m e:ℕ)(hr:R.t d ≤ m)(hm:m≤e)(he:e≤N)(c:ℝ)(hc:0≤c)
    (hp:∀ i:ℕ,  (m < i) → (i ≤ e) → Real.sqrt (R.alloy.B.a.clock.forcedAllowance i) ≤ c) :
      Within (books R W N p d m) (corridor R W h N p d e m) c := by
   induction hm using Nat.decreasingInduction with
   | self => exact vacant R W h _ _ hc
   | of_succ j hj ih =>
     have hw := hj.trans_le he
     have hT := ih (hr.trans j.le_succ) (fun i hi=> hp i (j.lt_succ_self.trans hi))
     rw [(placement R W h j hr hw (p:=p)).1,corridor,dif_pos ⟨hr,hj⟩]
     exact (payload R W h j hr hw (p:=p) _ _ c hT (hp _ j.lt_succ_self hj)).1

include h in
lemma pocket_book (s:ℕ) : ∀ᶠ m:ℕ in atTop, ∀ i:ℕ,(m ≤ i) → Real.sqrt (R.alloy.B.a.clock.forcedAllowance i) ≤ RG17.pocket R s m := by
   let A:= R.family.path.levels
   let Q:= A.clock.hatBeta
   have he := (Next.Rank.Station.hat_rate A h).eventually (Doors.stain_beats (s+1))
   obtain ⟨k,hk⟩ := eventually_atTop.mp he
   filter_upwards [eventually_ge_atTop k] with m hm i hi
   let b:= Real.sqrt (R.alloy.B.a.clock.forcedAllowance i)
   have hb(z):0<Q z:= zero_lt_one.trans (A.fits.delayed _)
   have hP:Q m ≤ Q i:= WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos h).le hi
   have hu:b*Q i^(s+1) ≤ 1:= hk i (hm.trans hi)
   change b ≤ (Q m)⁻¹^(s+1)
   rw [inv_pow, ← one_div]; exact (le_div_iff₀ (pow_pos (hb _) _)).mpr ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hb _).le hP _) (Real.sqrt_nonneg _)).trans hu)

variable (d:ℕ)
local notation "S" j=> (R.alloy.B.a.params j).columns
open RG17
/-- Result retains the full Coin seminorm, *even the forced divisor*,
 despite editing that input away at EVERY step. Works on arbitrarily long corridors
 with no cost from the number of times it is done. Native marks and labels of the FullVolume Run,
 including portals to the Final; heterogeneous schemes not used. Neighboring map
 estimate is in its own coordinates and summed products of these are not warranted. -/
theorem decksBooked (k:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ N p e:ℕ,  m ≤ e → e ≤ N →
       let x:=2^(k+1) * Pert.Asymptotics.regulatorRun R.family N p m^(2*(k+1))
       Within (books R W N p d m) (corridor R W h N p d e m) x ∧
        (m < e → ∃ hy:R.t d ≤ m,
         let P0:=stepTo R W h N p d m hy
         let r₁:=ruby d R.alloy.B.a m
         Costed (P0.leanings (books R W N p d (m+1))).toLinearMap
           (P0.leanings (soft (corridor R W h N p d e (m+1)))).toLinearMap (2*r₁*x) ∧
          2*r₁*x*(S (m+1)) ≤ x/2) := by
   filter_upwards [pocket_book R h k,eventually_ge_atTop (R.t d)] with m hm he N p e hr hp x
   have hZ:m ≤ N := hr.trans hp
   have hv:pocket R k m≤ x:= RG17.inPocket R k hZ
   have hx:0≤x:= (pocket_pos R k m).le.trans hv
   refine ⟨keep R W h m e he hr hp x hx (fun i h _=> (hm i h.le).trans hv),fun hi=> ?_⟩
   let P0:=stepTo R W h N p d m he; let r₁:=ruby d R.alloy.B.a m
   have hW:= keep R W h (m+1) e (he.trans m.le_succ) hi hp x hx (p:=p)
     (fun j hj _=> (hm j (m.le_succ.trans hj.le)).trans hv)
   obtain ⟨-,hP,hV⟩:= payload R W h m he (hi.trans_le hp) _ _ x hW ((hm _ m.le_succ).trans hv)
   have hi':2*r₁*x=r₁*x+r₁*x:=by ring
   exact ⟨he,(hi'.symm ▸ hP),show 2*r₁*x*(S (m+1)) ≤ x/2 from hi'.symm ▸ hV⟩

end YM.Pier.Mooring
