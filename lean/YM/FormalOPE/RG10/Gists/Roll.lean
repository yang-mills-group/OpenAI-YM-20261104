import YM.FormalOPE.RG10.Gists.Card
/-!
 # Compute joint cumulants in ordinary moment letter ring, covariance budget fully
 retained until post-transmission. Applied from each LOG cluster as one mark via all slot partitions.
 Requires NO inverse project/pinning, no root tests yet. WilsonX dictionary as in $Routes`.
 Also formulas for post-expanding in Kernel; integer stencil GPS to mesh geometry still producer. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gists
open Function PowerSeries Finset Route Gists.Word RG10.Word Marker
open Multi (Hot parts substitute shards unionOf)
open scoped Topology BigOperators Classical
open Card
variable {V : Type} [Fintype V] [DecidableEq V]
variable {I B J : Type} [Fintype J]
variable (e:Episode I B J)(R:Census V)

/-- Simple conditional moments, ONE same V output channel. -/
def moments (P:V→Channel I)(s:R.Mode) := e.floats (∏ x∈s.val,P x)
def cumulant (P:V→ Channel I) := logRow R (moments e R P)

/-- LOG->LOG. Use before stencil-cost multiplicity. These are full output logarithmic
 family; used arity projection rows for singleton instead require compatibility with input and
 budgets.L.Tips. Requiring formulae on actual tests. -/
def cumulLog (P: Hot R→Channel I) (s:R.Mode) := logRow R (fun s=>e.floats (program R P s)) s

variable (P:V → Channel I)
variable (Q:Hot R→Channel I)(s:R.Mode)
omit [Fintype V] in
lemma moments_blank : moments e R P R.quiet=1:= by simp [moments,Census.quiet]
omit [Fintype V] in
@[simp] lemma unit_null : cumulant e R P R.quiet=0:= rfl
omit [Fintype V] in
lemma spun_blank : e.floats (program R Q R.quiet) =1:= by simp
omit [Fintype V] in
lemma cumulLog_blank : cumulLog e R Q R.quiet=0:= rfl
lemma occupancy (y:B→ℂ) : run y (cumulant e R P s)=see s (logWord (seeOrd R (moments e R P) y)):= reading R _ y _ (moments_blank ..)
omit [Fintype V] in
lemma stepping (y:B→ℂ): seeOrd R (fun s=> e.floats (program R Q s)) y= parcel R (seeOrd (parts R) (moments e (parts R) Q) y) := by
 apply observe_ext; intro x; rw [parcels]; simp_rw [seen,program,_root_.map_sum]; rfl

lemma thruLog (y:B→ℂ): run y (cumulLog e R Q s)=see s (logWord (seeOrd R (fun x=>e.floats (program R Q x)) y)):= reading R _ y _ (spun_blank ..)
-- output cumul = sums of cumulant.Record.Engine.Log to future
lemma roll : cumulLog e R Q s=∑ t∈ shards R s,cumulant e (parts R) Q t := by
 apply runs_determine; intro y; rw [thruLog, _root_.map_sum]; simp_rw [occupancy];
 rw [stepping,←packup _ (revealed _ _ _ (moments_blank e (parts R) Q)), parcels]
lemma unfolds : e.floats (program R Q s)=program R (fun p: Hot R=>cumulLog e R Q p.val) s:= (moment_law R (fun s=>e.floats (program R Q s)) s (spun_blank ..)).symm
lemma unfolds_moments : moments e R P s=program R (fun p : Hot R=>cumulant e R P p.val) s:= (moment_law R _ s (moments_blank ..)).symm
-- still scalar check
end YM.FormalOPE.RG10.Gists
