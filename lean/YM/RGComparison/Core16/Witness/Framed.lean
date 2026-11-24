import YM.UVExtension.Reports.Ultraviolet
import YM.OPE.Columns.Accounts
import YM.OPE.Columns.Buy
import YM.OPE.Rough.Factory

/-!
# The UV cellar uses triangular towers (and so is eligible for the OPE/services pricing)

Apply with pre purchase `taller`. NB *not* a statement of sharp/log bound across levels! It says
that through true tuning this very cellar satisfies *the hypothesis of the ROUGH offshell estimates*
from OPE, not just some other Transfer with this same Wilson law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Witness
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open UVExtension PhysicalNext PhysicalNext.Repeat UVExtension.Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard UVExtension.Flake UVExtension.Mast
open Fitted
open Bid Next.Free Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
set_option quotPrecheck false
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A}
variable (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W) (v : Keys S)
    (d N m n:ℕ)
local notation "ℍ"=> Orchard.Path S v
local notation "s"=> A.B.a
local notation "F"=> (frames G).level d
local notation "B"=> localSection G d
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
local notation "b"=> C (A.B.a.clock.J (m+1))
local notation "K"=> A.B.a.S.block m
local notation "z₁"=> (A.B.a.params (m+1)).columns
local notation "x"=> Doors.rate (A.B.a.S.block m)
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)

/-- At every (real) offset the offshell tower tracks the canonical, triangular projection. -/
lemma lead_triangular : ∃ q : ℝ, Push.Local.Leading (Flake.leadF S R d N m hd).map.toLinearMap q := by
    unfold Flake.leadF; exact ⟨_, Seal.cap_lead B (sound G d) M.p.kernel.penalty_pos (A.B.a.clock.adm m) (Next.Foundations.valuation G d) (Warehouse.flight (Orchard.Path S (fun _ _=> Orchard.rose0 S)) N m) (le_trans (by omega : d ≤ A.B.a.clock.J m) (step_paid A.B.a m).1) (vision R d m hd)⟩

include hm in
set_option maxHeartbeats 800000 in
lemma lead_budget : let T:= Flake.leadF S R d N m hd; let L:= Mast.tide S R d N m n (v N n)
    (∀ y:(F).Coeff, (F).coeffSize (T.map y) ≤ b*(F).coeffSize y ∧
      (F).coeffSize (T.map.symm y) ≤ b*(F).coeffSize y) ∧
    Tips L K T x b:= by
    intro T L
    let H₀:= (ray S N n m (v N n) hm).body
    have hb₀ : Buys ℍ F W m b x := R.clock.fits ℍ rfl m d (by omega)
    have hu:= follows (hm:=hm) (hd:=hd) S R d N m n (v N n)
    have hp₀ := ponds S N n m (v N n) hm
    let H' := Orchard.Path S v
    let g0:= S.realBeat (v N n).val N n (m+1)
    have hp₁ : (H').rep N n (m+1) = g0:= rfl
    have hU:= palmLoop hm R.songs R.PStage R.wait (Graces.feet hd R.clock) (housed S v) R.r H₀ beam0 hp₀ hp₁ ((selected S v).represents N n m hm.le) hG R.tunes R.furthering R.corners R.shape R.clock R.stamp _ _ _ hu hd (zero_le_one.trans hb₀.cost) (vision R d m hd) (A.B.a.clock.adm m) ((le_trans (by omega : d ≤ A.B.a.clock.J m) (step_paid A.B.a m).1))
    rw [Push.PriceCompiler.block_eq A.B.valid]
    exact ⟨hU.1,hU.2.1⟩

/-- Paid before-L against *these* roll profiles. -/
def Headroom (Q:Levels G) : Prop := ∀ m d, d ≤ Q.clock.J (m+1) →
    let L:= Q.S.block m; let ε:= Doors.rate L
    ε * (1+2*(Q.params (m+1)).columns)* Motion.orbitCost ((frames G).level d) ≤ barunit L

include hm
variable {t:ℕ→ℕ}{U: Bolt A}(a:Upland.Arc X S U)(h:Lisle t A.B.a)
set_option quotPrecheck false
local notation "L!"=> cellar S R a t h
local notation "O!"=> hol G
open Motion

set_option maxHeartbeats 960000 in
lemma heads (h0: Headroom A.B.a) (ht:t d ≤ m):
    let T:= (L!).cantors v d n; let f:= (T.song N).tone
    let k:= Flake.leadF S R d N m ((h.tops d).trans (A.B.a.fits.mono ht))
    ∀ y:(F).Coeff, (F).coeffSize ( (f m).index y - k.leads K ((f (m+1)).index y)) ≤
       barunit K * (F).coeffSize ((F).core ((f (m+1)).index y)):=by
    intro T f k y
    let g:= T.lyr N (ht.trans hm.le)
    let aL:= fun (_:Motion)=> (L!).paths S v R d n m N
    let aY:= fun (_:Motion)=> g.Vista (m+1)
    let zz : (F).Coeff:= (f (m+1)).index y
    let q:= major aL aY (glaring A.B.a m n)
    have he:= (g.spaceF m ht hm y).1
    have hd:= (h.tops d).trans (A.B.a.fits.mono ht)
    have ht':∀ i z, ‖aY i z‖ ≤ z₁ * (F).coeffSize ((F).core z):= by
       intro i z; let h':= ht.trans m.le_succ; rw [show aY i z= _ from g.takes _ h' hm _]; exact g.climbs (m+1) h' hm z
    have hv' y: Tips (aL y) K k x b:= (lead_budget S R v d N m n hm hd).2
    change _=q zz at he
    rw [he]
    change (F).coeffSize (q zz - k.leads K zz) ≤ _
    have hh : d ≤ A.B.a.clock.J m := by omega
    apply (sailC aL aY (glaring A.B.a m n) hv' (zero_le_one.trans (A.B.a.params (m+1)).columns_ge) ht' zz).1.trans
    apply mul_le_mul_of_nonneg_right _ (Work.G08.size_nonneg ..)
    calc _ = x*(1+2*z₁)*orbitCost F:= by ring
         _ ≤ _:= h0 m d (hh.trans (A.B.a.fits.mono m.le_succ))

omit hm in
lemma framed (h0: Headroom A.B.a) : OPE.FramedColumns ((L!).yard v) W := by
    intro d N p hx m ht hm -- shadows not notation
    rw [show (fun y => ((((L!).yard v).factory d N p).entries (m+1) y).x)
          = fun y => (((((L!).cantors v d p).song N).tone (m+1)).index y) from ?_,
        show (fun y => ((((L!).yard v).factory d N p).entries m y).x)
          = fun y => (((((L!).cantors v d p).song N).tone m).index y) from ?_]
    · change t d ≤ m at ht; have hd:= (h.tops d).trans (A.B.a.fits.mono ht)
      refine ⟨Flake.leadF S R d N m hd, lead_triangular S R d N m hd,?_, heads S R v d N m p hm a h h0 ht⟩
      intro y
      have Hz:= (lead_budget S R v d N m p hm hd).1 y
      let x' := C (A.B.a.clock.J (m+1)); let u:= Doors.rate (A.B.a.S.block m)
      let F':=(frames G).level d
      have hc:= R.clock.fits ℍ rfl m d (by omega)
      have hx : 1 ≤ x':= hc.cost
      have he:x'≤x'+u*(A.B.a.params (m+1)).columns:=le_add_of_nonneg_right (mul_nonneg (Doors.rate_pos ..).le (zero_le_one.trans (A.B.a.params (m+1)).columns_ge))
      have hu:= (he.trans (le_mul_of_one_le_right ((zero_le_one.trans hx).trans he) (orbitCost_one_le F'))).trans hc.funds
      have hv:=mul_le_mul_of_nonneg_right hu (Work.G08.size_nonneg F' y)
      exact ⟨(Hz.1).trans hv, (Hz.2).trans hv⟩
    all_goals
      let T := ((L!).cantors v d p|>.song N).tone
      have he(i:ℕ)(hi:t d ≤ i)(hv:i ≤ N) : (fun y=> ((((L!).yard v).factory d N p).entries i y).x) = (T i).index := by
        have hh :=(Cellar.launch v L! d N p).choose_spec hx|>.2
        change (fun y=> (((L!).gate v d N p).entries i y).x) = _
        rw [show ((L!).gate v d N p).entries=_ from hh]
        exact funext (((L!).cantors v d p|>.lyr N hx).earned.earned i hi hv).currents
      first | exact he m ht hm.le | exact he (m+1) (ht.trans m.le_succ) hm

end YM.RGComparison.Core16.Witness
