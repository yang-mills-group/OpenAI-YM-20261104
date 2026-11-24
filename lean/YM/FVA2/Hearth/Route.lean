import YM.FVA2.Hearth.Choice
import YM.FormalOPE.RG10.Transit.Merits
/-!
# Bridge to `Route.Bulk`

We use the actual Engine implementation in RG10. For any step in the given setup, no
assertion of *uniform* prices. Keep the `income` identity at open field, so
`transferance` preserves the **full** denominator. This doesn't set all unmarked
inputs to zero before doing the step, or omit the mean in conditioning.
Use `pantry`, etc., and `Arrival/Episodes` for the reading from the other side
of this interface (namely `Lumen.Fk.valuation`,`Lumen.Fk.read` in `Core16`).

For how to continue those evaluations and obtain Wilson as in the manuscript, see
`YM/FVA2/Handoff.lean`. For that comparison use also the same clock information
(`Hearth/Clock.lean`). No analytic or cutoff-uniform convergence results here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open Sync
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side} {L:Fabric G n}

section
abbrev Streets (G:Gauge)(n:Side):= OEdge n × Space G.Color

variable {J:ChartRatio G}
section
variable {S:StepData c f}(t:S.Choices)(P:Inside S.ratio)
variable {I B:Type} [Fintype I] [Fintype B] (x:Layout I (Flats G f))(y:Layout B (Flats G c))
variable (U:Unmasked G f)(p:PowerSeries ℝ)(q:(core (gated P U t p)).RespectsPrice)
variable (u:incline U.W)(hj:LocalRatio J)(A:Ticket (Flats G f))
include u hj
local notation "E"=> Engine J t P x y p U q
lemma synch : digital y (Update P t J p U q).W=Route.Bulk.income (E).joint (E).vertices := by
 let V:=receipt P t J p U
 let μ:= tangent G (Blocking.Index S P)
 let b:= center _ q
 change digital y (uptake _ μ q _) = _; rw [Sync.stationed]; exact (Sync.revenue q.inner x y (OpenSlots.extend P) (threadTo P) (boost b V) (pursue P) μ (preserve_boost _ (OpenSlots.along hj p u))).symm
lemma transferance : digital y (Broadcast P t J p U q (boost (blankRight P) A))= Route.Bulk.transfer (E).joint (Route.replot (E).spur (digital x A)) (E).vertices := available J t P x y p U hj u q A
-- Slot objects.Schema explicit point powers (can recover real valuations at Layout tint; use displacement scaling of Ops)
lemma steps (a:B→ℂ) : let F := Joins.Gauss.standardFeed (Space (Cross (G:=G) S P));
 Route.run a (digital y (Broadcast P t J p U q (boost (blankRight P) A))) = F.step (Route.Bulk.intake (E).joint a (E).vertices (E).law) (Route.Bulk.water (E).joint a (Route.replot (E).spur (digital x A))) ∧
 Route.run a (digital y (Update P t J p U q).W)= F.den (Route.Bulk.intake (E).joint a (E).vertices (E).law):= by
 rw [synch t P x y U p q u hj, transferance t P x y U p q u hj]; exact ⟨Route.Bulk.unfolds_step ..,Route.Bulk.enters ..⟩ -- order
end

open Route
local notation "D(" n ")"=> natural n G
 def channelTransit {n:Side}{L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(A:Channel (Streets G n))(J:ChartRatio G)(h:Commission J T U z): Channel (Streets G (Bottom L)):= match T with
 | .floor _ _ _=> A
 | .inLayer (c:=c) (L:=M) (t:=t) P C=> show Channel (Streets G (Bottom M)) from
   let r:= (show (core (gated P U t (z none))).RespectsPrice from Exists.choose h)
   channelTransit (L:=M) C (z∘some) (Update P t J (z none) U r) ((Engine J t P D(n) D(c) (z none) U r).floats A) J (Exists.choose_spec h)

theorem centeredTransit {n:Side}{L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(A:Ticket (Flats G n))(h:Commission J T U z)(hj:LocalRatio J)(u:incline U.W):
 channelTransit T z U (digital D(n) A) J h= digital D(Bottom L) (drive T z U A J h).2:= by
 cases T with
 | floor=> rw [drive]; rfl
 | @inLayer c f S H t hf L P C=>
    rw [drive,channelTransit];
    let b:= Exists.choose h; let V:= Update P t J (z none) U b; let S:= Engine J t P D(n) D(c) (z none) U b; let p:=Exists.choose_spec h
    let A':= Broadcast P t J (z none) U b (boost (blankRight P) A)
    have he: S.floats (digital D(n) A)=digital D(c) A':= (available J t P _ _ _ U hj u b A).symm
    change channelTransit C (z∘some) V (S.floats _) J p=_; rw [he]; exact centeredTransit C _ V A' p hj (funded hj (z none) u _)
termination_by structural T

-- actual finite dependence and Guard degree. expose rank even before scheduling price.Similar circuits.J
lemma channelThrough {n:Side}{L:Fabric G n}(T:Cloth L){z:L.Cost→PowerSeries ℝ}{U:Unmasked G n}(h:Commission J T U z) (k:ℕ){A B:Channel (Streets G n)}(he:Through k A B): Through k (channelTransit T z U A J h) (channelTransit T z U B J h):= by
 cases T with
 | floor=> rw [channelTransit,channelTransit]; exact he
 | inLayer P C=>
    rw [channelTransit,channelTransit]; exact channelThrough C _ k (transmitter _ _ he rfl rfl (Through.refl _))
termination_by structural T
variable (T:Cloth L)(z:L.Accounts→PowerSeries ℝ)(hz:∀i,0<term (z i) 0)(hj:LocalRatio J)
local notation "q"=> collared T z hj hz
-- `Eligible` certified for each input of guarded rank via Sync; our actual observation at fixed family of marks meets it exactly (for unshifted rank). Tests throughout retain positions.
lemma guarded (O:Wilson.Config G n→ℝ) : Coherent T J (headquarters z) (imprintRoot O) (z∘some) q 0:= by
 apply Sync.persist
 · exact hj
 · exact Sync.stock.rising _
 · exact Sync.root _
 · exact OpenSlots.restores ..
variable (v:L.Accounts→ℝ→ℝ) (a: G.ColorIndex)(y:Flats G (Bottom L))
variable (N:ℕ)(hv:∀ i,ContDiffAt ℝ ω (v i) 0)(h:∀i,Through N (amount (v i)) (z i))
include hv h
local notation "P"=> localClimate T y a v
-- Through the announced order.
theorem pantry (O:Wilson.Config G n→ℝ)(hO:PreTest O): Through N
 (Sync.align (PowerSeries.mk (Lumen.Fk.valuation P J (tease T a) (lens T y a (rad T O)))))
 (Route.run (Sync.tint D(Bottom L) y) (channelTransit T (z∘some) (headquarters z) (digital D(n) (imprintRoot O)) J q)):= by
 rw [centeredTransit T _ _ _ q hj (OpenSlots.restores ..), Sync.accessing]
 intro i hi; unfold Sync.align; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,predicts T y a v hj z hz N hv h O hO _ hi]
end
end YM.FVA2.Hearth
