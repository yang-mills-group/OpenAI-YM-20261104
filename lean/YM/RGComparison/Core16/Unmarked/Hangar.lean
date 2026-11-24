import YM.RGComparison.Core16.Unmarked.Pressure
import YM.UVExtension.Oasis.Flora
import YM.RGComparison.Core16.Binding
/-!
# Bind the unmarked steps to the Context

Proof source of every `credit` cost. No identifying with a ghost or
renumbering according to values. Family path:: @roseA; exactly that kalender. Receipt for using
models even without step estimates that they're reachable by shipping, independent
of exact finite-period or top selected value. Transfer necessary for using local hypothesis.
Working in counterterm sign + as in Thermal; not claiming F/B condition beyond current hypotheses.
Pull from the very same patches and period. This maximizes structural continuity by keeping the
'Mast' union.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open Push.Uniform Input Org Supply Pane Progress.DirectedRecipe
open ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open UVExtension UVExtension.Guild UVExtension.Concert UVExtension.Spire UVExtension.Dales UVExtension.Camp.Cart UVExtension.Lamppost UVExtension.Oriel
open UVExtension.Mast
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G:Gauge}{hG:G.Simple}{C:Family G}

/-- Instantiate with `.fitting`. Exposes exact choice of unmarked iteration prescription from this Union. -/
structure Hangar (C:Family G)(hG:G.Simple) where
    M:Metals G
    P:Rolls M.p
    A:Alloy M P
    R:Roost.Factor A
    S:Uses R hG
    history:Bolt A
    reach: Upland.Arc R S history
    t:ℕ→ℕ
    K:ℕ→ℝ
    w:Bid.Worth
    Q: Legato.Bandage R K w
    L: Mast.Cellar S t Q
    floral: Oasis.Spring S
    final: C=Mast.Cellar.yard (Mast.roseA S) L

/-- `G, hG, b, E` fixed, not choosing different Supports families for Rep. -/
lemma Context.fitting {b:ℝ} (E: Context G hG b): Nonempty (Hangar E.C hG):=by
    obtain ⟨X,Y,A,R,S,F,t,K,k,B,H,L,he,hO,-⟩:= E.floral
    exact ⟨⟨X,Y,A,R,S,F,L,t,K,k,B,H,hO,he⟩⟩
lemma Hangar.actual (H: Hangar C hG) : C.path=H.A.B.bake.make (H.S.realBeat 0):= congr_arg Family.path H.final

namespace Unmarked
variable {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A}
   (S: Uses R hG) (N p : ℕ)
local notation "a!"=>A.B.a
set_option quotPrecheck false
-- lean parser parentheses
local notation "H₁"=> (S.fits N p)
local notation "Q₁"=> S.grove.coins
local notation "B₁"=> (S.cart N p)

/-- offset zero (local lever at origin of bar). -/
abbrev meter (m:ℕ) := (S.realBeat 0 N p m).beta
abbrev income (m:ℕ) := (S.realBeat 0 N p m).v
abbrev field (m:ℕ) : Render S m N p:= (H₁).Rest B₁ Q₁ 0 m

def measured (i:ℕ) := field S N p i

lemma at_home (i:ℕ) : enact (measured S N p i) (meter S N p i) (income S N p i) = S.realBeat 0 N p i:= rfl
lemma stationed : Fitted.Shot (S.fits N p) (measured S N p) (meter S N p) (income S N p) ∧ meter S N p 0=(a!).clock.bar+(0:ℝ):=
    ((H₁).acts B₁ (S.token N p) Q₁ (Uses.centerP _))
lemma favors {i:ℕ} (he:i≤N): UVExtension.Lamppost.InsideB ((a!).clock.hatBeta i) (meter S N p i) ∧ credit S (measured S N p i) ≤ UVExtension.Camp.soft:= by
    obtain ⟨hx,hv⟩:= stationed S N p
    exact ⟨(H₁).rootc hx (Uses.centerP _) hv i he,( (UVExtension.Spire.Fitted.plates S.grove.enabled S.grove.climbed (H₁) hx (Uses.centerP _) hv i he)).1⟩
lemma billing {i:ℕ} (he:i≤N): Favored (measured S N p i):= (favors S N p he).2.trans_lt (by norm_num [UVExtension.Camp.soft,rim])

lemma top : measured S N p N= Dales.city R (S.grove.rise N) S.grove.peak ((stationed S N p).1.alive N le_rfl|>.1) (H₁|>.start):= (H₁).top_mom (stationed S N p).1
lemma receipt {i:ℕ}(hi:i<N): let Q:= S.realBeat 0 N p i
    let x:= measured S N p (i+1); let b:= meter S N p (i+1)
    course hi x b=measured S N p i ∧ b+surge hi x b=meter S N p i ∧ run hi x b (income S N p (i+1))=Q := by
    intro Q x b; let H:=(stationed S N p).1; have he:= UVExtension.Spire.Fitted.doors (S.fits N p) H i hi; have hz : Reality a! (i+1) p ((H₁).W (i+1)) x b:= H.alive (i+1) hi
    rw [operated hi x _ hz, course, Tour.choiceV, dif_pos hz]
    refine ⟨he.2.1.symm,?_,(H.passes _ hi).symm⟩
    unfold surge; rw [Tour.claim, dif_pos hz, ←add_assoc]; exact he.1.symm
end Unmarked
end YM.RGComparison.Core16
