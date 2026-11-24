import YM.OPE.Compatible.Frog.Scalp
/-!
# Push in Lane orders
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ} {C:KernelChoices}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ} {P:Patch}
variable (b:ℝ)(A:Alps K T i v)(U:Boxes G P C)(R:ChartRatio G)
variable (h:RollD A U R)(hp: Aware d τ)
include h
local notation "L(" p ")"=> sculpt P C U A R b p d
lemma offered (p:T!)(hp:Aware d τ): spread G d τ (actor A U R b h hp p)=L(spread G d τ p):=by
      let f(j:Phase):= pointer G d j (τ j) (p j); have hf(i:Phase): Tide (f i) d 45 ‖p i‖:=fun j=> VolumeWe (pointerFee (m:=τ i) i (p i) j) (awareLeaf hp _)
      have H(t:Finset Phase)(ht:t.Nonempty): L(∑ i∈t,f i)=∑ i∈t,L(f i):=by
           induction t using Finset.induction_on with
           | empty=> exact (not_nonempty_empty ht).elim
           | insert i s hi ih=>
               by_cases hs:s.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hs]; simp
               rw [sum_insert hi,sum_insert hi, ← ih hs]; exact levy P C U A R b h.eph h.flea h.jar le_rfl (hf i) (α:= _) (β:=∑ i∈s,‖p i‖) (by intro j; rw [Finset.sum_apply]; exact Volume.sum _ _ _ fun _ _=> hf _ _)
      funext k; change lilies _ _ _ (actor A U R b h hp p k)= _; rw [actorA, map_sum,pointers,show sculpt _ _ _ _ _ _ _ _= _ from H univ Finset.univ_nonempty, Finset.sum_apply]; exact Finset.sum_congr rfl fun _ _=> actsP b A U R h hp ..
lemma actors (p:T!)(hx:p∈solar G d τ): actor A U R b h hp p∈ solar G d τ:=by
     change Rainbow _ ∧ Pathic d _; rw [offered b _ _ _ h p hp]; let x:=spread G d τ p; have he := scours h.jar U h.flea d 45 x ‖p‖ le_rfl hx.2 (resin p (m:=45) (awareLeaf hp)) h.eph b; obtain ⟨g,a,hv⟩:=he; refine ⟨rainbow P C U A R _ b, fun n z=>?_⟩; erw [bustDD P C U A R x a b z hv]; exact g n z
     -- ...
lemma acceptZ (j y:Phase)(hx:j<y): Drift.chamber A U R b y j h hp=0:=by unfold Drift.chamber; rw [dif_neg (by order)]
omit h in
lemma reacquire (x:Phase): glasses (Shade G) (d+x.val) (τ x) (τ x) le_rfl=1:=by -- Glass namespace check
     apply ContinuousLinearMap.ext; intro p; apply lilies_inj _ _ _; rw [putG,forgets];rfl
