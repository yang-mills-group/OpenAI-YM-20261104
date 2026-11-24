import YM.QuadraticLocal.Earn.Cable
import YM.Push.ABSOLUTE_SUMS.Animals
/-! # Census metadata for the exponential kernel budget

 Our native budgets keep COMPLETE label layouts even at a fixed regulated epoch.
 For the fundamental Marker Θ representing a stencil choose its support including any
 addressed tests in advance. Use among its stature numbers any other initialization
[cost], e.g. true lifted lengths of addresses. This posture during a phase
 (can freeze many epochs of stencil data with many markers) doesn't infer the budget
 of a render from sharing a certificate of such root locations. λ rows still pay
 exact occurrence costs. Canonical sections referring to different addresses should
 be launched with their own witnesses in that reconstruction; don't minimize over a stencil
 while taking successive estimates or re-projecting kernels.

 Through projection only `support` is literal image and subsequent wallet uses the inherited
 test-coordinate. No charts inferred from that support homomorphism.
 All mark origins paid. The marker-support epoch precedes all test inputs; ABI `Long` also
 accounts sum of the reserve lengths supplied here with multiplicities. No enabling
 keys on unbooked wallets, then dropping their costs at readout. Root/name/test movement on
 general Ward transforms (if Rerouting) can incur its own further multipliers; lifetime here is
 on one set of charged stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Push Push.AbsoluteSums Paths
open Cable
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {c n : Side} {V ι : Type*} {a k :ℕ}

structure Passport (n:Side)(V:Type*) where
   origin : V→Site n
   support : V→Support n
   wire : V→Walk
   height : V→ℕ
   born v : origin v∈ support v
   visits v : support v ⊆ Paths.native (origin v) (wire v)
   room v : (wire v).length≤height v

namespace Cable
variable (q : Ratio c n)
-- deterministic for wiring render so also transport support IDs. Doesn't delete old walks.
lemma mass_mono : Monotone (Cable.mass q) := fun _ _ h=> Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.div_le_div_right h) _)
def follows (x:Site n) (w:Walk): Walk:=(caravan (x:=x) q w).choose
lemma follows_tip (x:Site n)(w:Walk) : stop (q.parent x) (follows q x w)=q.parent (stop x w):=(caravan (x:=x) q w).choose_spec.1
lemma follows_path (x:Site n)(w:Walk) : (Paths.native x w).image q.parent ⊆ Paths.native (q.parent x) (follows q x w):=(caravan (x:=x) q w).choose_spec.2.1
lemma follows_bound (x:Site n)(w:Walk) : (follows q x w).length ≤ Cable.mass q w.length:=(caravan (x:=x) q w).choose_spec.2.2
variable (u:ℕ)
lemma fare : q.count.val * Cable.mass q u ≤ Cable.links * (q.count.val + u) := by
   unfold mass; let x:= q.count.val; have hv:x*(u/x)≤ u:= by simpa only [Nat.mul_comm x] using Nat.div_mul_le_self u x
   calc q.count.val*(links*_) = links*(x+x*(u/x)):= by dsimp only [x]; ring
        _ ≤ _:= Nat.mul_le_mul_left _ (Nat.add_le_add_left hv x)
end Cable

variable (P:Passport n V)
namespace Passport
def coarser (q : Ratio c n) : Passport c V where
    origin := q.parent ∘ P.origin
    support v:= (P.support v).image q.parent
    wire v:= follows q (P.origin v) (P.wire v)
    height := Cable.mass q ∘ P.height
    born v:= Finset.mem_image_of_mem _ (P.born v)
    visits v:= Subset.trans (Finset.image_subset_image (P.visits v)) (Cable.follows_path ..)
    room v:= (Cable.follows_bound ..).trans (Cable.mass_mono q (P.room v))
-- installation: allow v multiple copies, pay with their tests and REAL roots carried at all CHILD phases. Check stage schedule Status grants. canonical point case

def point (o:V→Site n) : Passport n V where
   origin := o
   support i:={o i}
   wire _:=[]
   height _:=0
   born i:=mem_singleton_self _
   visits i:= by simp [Paths.native, Lattice.visits]
   room i:= le_refl _
end Passport
section kernels
open RG
variable [DecidableEq V] (R:Marker.Census V)
-- meta + extra width budget for inherited winding ancestry. Require certificate on retained
-- walks themselves, not just existence of another sufficiently short connector. Choose any orientation ahead of budget.
structure Binder where
   mode : R.Mode
   front : V
   east : front∈mode.val
   path : V → Walk
   span v : v∈mode.val → stop (P.origin front) (path v) = P.origin v
   extra : ℕ
namespace Binder
variable {R P}{G:Gauge}
variable (A:Binder P R)(J:Atom G k)
set_option quotPrecheck false
def center : Site n:= P.origin A.front
lemma live : A.mode≠ R.quiet:= fun hh=> Finset.notMem_empty A.front (by change A.front∈R.quiet.val; rw [←hh]; exact A.east) -- type?
def distance (i:V):ℕ:= (A.path i).length+P.height i
-- true frame including tests; billing at ALL V

def length := A.extra+(∑ i∈A.mode.val,A.distance i)
-- one walkthrough including T v

def leg (v: V) := Paths.native A.center (A.path v ++ P.wire v)

def ground := J.footprint A.center ∪ A.mode.val.biUnion A.leg

lemma first : A.center∈ A.ground J:= mem_union_left _ (Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩) -- rewrite
lemma capacity (i:V)(hi:i∈A.mode.val): stop A.center (A.path i)=P.origin i:=A.span i hi
lemma footprint : J.footprint A.center ⊆ A.ground J:= Finset.subset_union_left
lemma remembered (v:V)(hv:v∈ A.mode.val): P.support v ⊆ A.leg v:= Subset.trans (P.visits v) (by rw [leg,Native.combine,A.capacity v hv]; exact Finset.subset_union_right)
lemma covers (v:V)(hv:v∈A.mode.val): P.support v⊆ A.ground J:= Subset.trans (remembered A v hv) (Subset.trans (Finset.subset_biUnion_of_mem A.leg hv) Finset.subset_union_right)
lemma dues (v:V)(hv:v∈A.mode.val): A.distance v ≤ A.length:= (Finset.single_le_sum (s:=A.mode.val) (fun i _=> Nat.zero_le (A.distance i)) hv).trans (Nat.le_add_left ..)
lemma rate (v:V) : (A.path v ++ P.wire v).length ≤ A.distance v:=by rw [List.length_append]; exact Nat.add_le_add_left (P.room v) _
-- airport radius cap from weak geometry
variable {i M :ℕ} {z: Site n}
lemma spread (h : z∈ A.ground J): separation A.center z ≤ A.length + J.length := by
   rcases mem_union.mp h with h|h; rw [Paths.atom_foot] at h; exact (Paths.where_slot A.center J.leg z h).trans (Nat.le_add_left ..)
   obtain ⟨v,hv,h⟩ := mem_biUnion.mp h; exact (Paths.to_ball _ _ h).trans ((A.rate v).trans ((A.dues v hv).trans (Nat.le_add_right ..)))
lemma charge (hM:0<M) : M * coverNumber M (A.ground J) ≤ (1+k+A.mode.val.card)*M + J.length + A.length:=by
   let u:=A.center; let D(s:Finset V):= J.footprint u∪s.biUnion A.leg
   have he(s:Finset V): M*coverNumber M (D s) ≤ (1+k+s.card)*M + J.length+∑ i∈s,A.distance i:=by
      induction s using Finset.induction with
      | empty => rw [sum_empty,card_empty,Nat.add_zero,Nat.add_zero]; unfold D; rw [biUnion_empty,Finset.union_empty,Paths.atom_foot]; exact Paths.size u J.leg hM
      | insert i s hi IH=>
          have hz:u∈D s:= Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩)
          rw [show D (insert i s)=D s∪ A.leg i from by unfold D; rw [Finset.biUnion_insert,Finset.union_assoc,Finset.union_comm (s.biUnion _)], card_insert_of_notMem hi,sum_insert hi]
          refine (Nat.mul_le_mul_left M (Corona.meets_sum hz (show u∈ A.leg i from Native.first u _) M)).trans ?_
          calc M*_ = M*coverNumber M (D s)+M*coverNumber M (A.leg i):= by ring
               _ ≤ _:= (Nat.add_le_add IH ((Paths.native_cover u hM _).trans (Nat.add_le_add_left (A.rate i) _))).trans_eq (by ring)
   refine (he A.mode.val).trans ?_; show _ + _ ≤ _+ A.length; exact Nat.add_le_add_left (Nat.le_add_left ..) _
end Binder
end kernels
end YM.QuadraticLocal.Earn
