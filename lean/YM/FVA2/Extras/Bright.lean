import YM.FVA2.O.Hue.Filled
import YM.FVA2.O.Rough.Vault
/-!
  # Additional MS columns. First, two-sided all-momentum window prices

  Studying the appropriate `nav` on these fields (using `M`). Below we will use
  this to analyze the redundancy convention for the **physical projection** of any extra
  closed mark row, e.g. any submission within `Mach.Ele`. Extra columns are not required for
  `physical_compare` to `MS_Data`.

  This analysis also covers the more general case of `Dock.comet` on any
  classical `Schema` input (all ranks and parities as in `Schema`) with the closure
  `Emit.Trill`. We do not define any new dimensional continuation prescription.

  Intervals for **this proof** = all ℝ! Thus can infer exact hard polynomial shape at first
  nonvanishing rank/order. For corresponding results after specializing/reducing
  those insertions see `Extras/Result`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
variable {I:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{F:Glade G Unit}
variable {b d:ℤ}{r k n:ℕ}{u:ℝ}{X Y:T ( Glade G Unit )}

def FullEra (u:ℝ): Home ℝ Unit := {
    basic r:=1+‖u‖+‖r‖
    one_le r:=by linarith [norm_nonneg u,norm_nonneg r]
    length t:= exp t
    pos := exp_pos
    pick _:=()
    t t:= t
    slot _:=rfl }
local notation "T₁"=> (FullEra u)
abbrev logMass (u:ℝ) (_:Unit) := u
lemma liveFull : liveP T₁ (logMass u):= fun t=> (norm_add_le ..).trans (by change ‖u‖+‖t‖≤1+‖u‖+‖t‖; linarith [norm_nonneg u])
-- exposed radius on this scale.
abbrev Clean (u:ℝ)(F:Glade G Unit)(d:ℤ): Prop:= Latch.Lease false false (FullEra u).toScale ( sendT (FullEra u) F ) ( fun i=> (FullEra u).length i^(-d) )
abbrev Honest (u:ℝ)(X:T (Glade G Unit))(d:ℤ) : Prop:= ∀ i,Clean u (X i) d
lemma Honest.zero : Honest u (0:T ( Glade G Unit )) d := fun _=> Latch.Lease.zero (fun _=> length_p ..)
lemma Honest.plus (h:Honest u X d)(he:Honest u Y d): Honest u (X+Y) d:= fun n=>(h n).plus ( he n )
lemma Honest.sub (h:Honest u X d)(he:Honest u Y d) : Honest u (X-Y) d:= fun n=>(h n).minus (he n)
lemma Honest.raise (h:Honest u X d)(k:ℕ): Honest u (Hue.hold0 k X) d:= by intro i; by_cases hi:k≤ i; rw [ Hue.hx_holder hi ]; exact h _; rw [ Hue.low_hold (by omega) ]; exact Honest.zero i
lemma Honest.cost (h:Honest u X d)(a:ℝ): Honest u (Hue.seat (fun _=>a) X) d:= fun i=> ( h i ).cash (a:ℂ)
lemma cometClean {Q D:CostsM G}{Y:Blue G}(he:Dock.comet k b M.bulk Q Y D): Honest u ( letIn k (logMass u) Y ) k:= fun _=> ageM liveFull he
-- main d estimate on differential
lemma proper_X {d:ℤ}(he:Clean u F d): Clean u ( (both G Unit).C (Lives.gather M (logMass u) n) F ) (d+1):= by
    refine Latch.Lease.sticks ( trunks ( K:=fun i=>lineB G ((FullEra u).t i) ) ( fun i j=> Latch.polar (capeB T₁ G i j) ) ( ageB (M:=M) liveFull ) he.highp (true_nn T₁) (fun _=> length_p ..) (fun _=> length_p ..) ) (fun i=>?_); simp only [positive, TrueT, Pi.mul_apply]; rw [neg_add_rev,zpow_add₀ ((FullEra u).pos i).ne']; exact le_of_eq (by field_simp [((FullEra u).pos i).ne'])
lemma proper_V {d:ℤ}(hp:Warm F false)(he:Clean u F d): Clean u ((both G Unit).J F) (d+1):= by
    have hs : Latch.Lease false false (FullEra u).toScale (sendT T₁ ((both G Unit).J F)) (TrueT T₁ * (fun t=> (FullEra u).length t^(-d)) ):= by
        rw [front G Unit,LinearMap.add_apply]; apply Latch.Lease.plus ?_ ( poses (fun r _=>?_) );
        · refine Latch.Lease.sticks ( O.Cool.lease_Q (η:=(FullEra u).t) (FullEra u).slot he (fun _=>length_p ..)) (fun i=>?_); simp only [TrueT,Pi.mul_apply,Cool.stamp]; rw [zpow_neg_one]
        rw [ spine hp realityB ]; exact penny ( pinch he (fun i=>Bool.noConfusion i) ) (fun _=>length_p ..) (capeB T₁ G) (true_nn T₁) ( Tall _ 5 (by omega)) (fun E _=>tom _ 5 (by omega))
    refine Latch.Lease.sticks hs (fun i=>?_); simp only [TrueT, neg_add_rev, Pi.mul_apply,zpow_add₀ ((FullEra u).pos i).ne',zpow_neg_one,le_refl]
lemma proper_B (he:Honest u X d): Clean u ( pairW (both G Unit).C (Lives.gather M (logMass u)) X n ) (d+1):= by
    rw [paired]; generalize W : antidiagonal n = Z; clear W; induction Z using Finset.induction_on with
    | empty=> rw [ Finset.sum_empty ]; exact Honest.zero 0
    | insert x s hi ih=> rw [ Finset.sum_insert hi ]; exact Latch.Lease.plus ( proper_X ( he x.2 ) ) ih
lemma Honest.nav (hh:Honest u X d)(hx:Response X M (logMass u) b): Honest u (nav M (logMass u) X) (d+1):= fun i=> Latch.Lease.plus ( proper_V ( hx.life i|>.cross ) ( hh i )) (proper_B hh)
end YM.FVA2.Extras
