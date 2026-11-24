import YM.Integration.WilsonOriginalAlternativeStamped
import YM.Integration.WilsonOriginalAlternativePeerFields

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTelescope
open Finset Function Lattice Wilson RG Marker QuadraticLocal
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction WilsonOriginalAlternativeHearing
open WilsonOriginalAlternativeHybrids
open scoped Classical BigOperators

variable {V:Type} [DecidableEq V]

/-- At each change, the remaining original names are exactly the suffix of the elected order. -/
def tally (D:V → Finset V → ℂ) : List V → ℂ
  | [] => 0
  | v :: tail => D v tail.toFinset + tally D tail

private theorem telescope (H:Finset V → ℂ) (D:V → Finset V → ℂ) (s:Finset V)
    (step:∀j∈s,∀X:Finset V,j∉X → D j X=H (insert j X)-H X)
    (l:List V) (active:∀j∈l,j∈s) (once:l.Nodup): H l.toFinset - H ∅ = tally D l:=by
  induction l with
  | nil => simp [tally]
  | cons j l ih =>
    obtain ⟨out,rest⟩:=List.nodup_cons.mp once
    have out':j∉l.toFinset:=by simpa using out
    have at':j∈s:=active j (by simp)
    have rem:=ih (fun v hv=>active v (by simp [hv])) rest
    rw [tally,step j at' l.toFinset out',←rem,List.toFinset_cons]
    abel

private theorem money (D:V → Finset V → ℂ) (fee:V → ℝ) (s:Finset V)
    (cash:∀j∈s,∀X:Finset V,X⊆s → j∉X → ‖D j X‖ ≤ fee j)
    (l:List V) (active:∀j∈l,j∈s) (once:l.Nodup): ‖tally D l‖ ≤ ∑j∈l.toFinset,fee j:=by
  induction l with
  | nil => simp [tally]
  | cons j l ih =>
    obtain ⟨out,rest⟩:=List.nodup_cons.mp once
    have out':j∉l.toFinset:=by simpa using out
    have at':j∈s:=active j (by simp)
    have keep:∀v∈l,v∈s:=fun v hv=>active v (by simp [hv])
    have inside:l.toFinset⊆s:=fun v hv=>keep v (by simpa using hv)
    simp only [tally,List.toFinset_cons,Finset.sum_insert out']
    exact (norm_add_le ..).trans (add_le_add (cash j at' l.toFinset inside out') (ih keep rest))

variable [Fintype V] {G:Gauge} (C:Family G) {N p k f:ℕ}
  (J:Census V) {T μ:Type} {W:Rep G (C.side k p)} {o:V→Site (C.side k p)}
  (A:Gallery T μ (o∘Prod.fst) W (board J)) (F:T → Config G (C.side k p) → Poly J)
  (B:T → Config G (C.side k p) → V → ℂ) (x:T) (s:J.Mode) (lower:f ≤ k) (U:Config G (C.side f p))

def charge (v:V) (X:Finset V):ℂ := held C N p (fun Y=>
  ((F x Y).part (live J s (insert v X))-(F x Y).part (live J s X)*B x Y v)*
    ∏z∈s.val\(insert v X),B x Y z) lower U

private def amount (X:Finset V):ℂ:=held C N p
  (fun Y=>(F x Y).part (live J s X)*∏z∈s.val\X,B x Y z) lower U

include A in
private theorem step (field:∀Y,A.density x Y=stamped J (F x Y) (B x Y))
    (seen:WilsonOriginalAlternativeStamped.Heard C N p k J A F B) (v:V) (inside:v∈s.val)
    (X:Finset V) (out:v∉X):
    charge C (N:=N) J F B x s lower U v X =
      amount C (N:=N) J F B x s lower U (insert v X) - amount C (N:=N) J F B x s lower U X:=by
  let g (c:V→Port):=held C N p (source C p J A x c s) lower U
  have both (Y:Finset V):g (WilsonOriginalAlternativeHybrids.route Y)=amount C (N:=N) J F B x s lower U Y:=by
    apply congrArg (fun y=>held C N p y lower U)
    funext t
    simp only [source,field]
    exact WilsonOriginalAlternativeHybrids.original J (F x t) (B x t) Y s
  have inc:Function.update (WilsonOriginalAlternativeHybrids.route X) v 0=
      WilsonOriginalAlternativeHybrids.route (insert v X):=by
    funext z
    by_cases eq:z=v
    · subst z;simp [WilsonOriginalAlternativeHybrids.route]
    · simp [WilsonOriginalAlternativeHybrids.route,eq]
  have exc:Function.update (WilsonOriginalAlternativeHybrids.route X) v 1=
      WilsonOriginalAlternativeHybrids.route X:=by
    funext z
    by_cases eq:z=v
    · subst z;simp [WilsonOriginalAlternativeHybrids.route,out]
    · exact Function.update_of_ne eq ..
  have row:=seen x f lower U s
  have swap:=row.2.2.2 v inside (WilsonOriginalAlternativeHybrids.route X)
  change g _=g _-g _ at swap
  rw [inc,exc,both,both] at swap
  exact (congrFun (WilsonOriginalAlternativePeerFields.original J C A x (F x) (B x) field s X v out inside lower) U).symm.trans swap

include A in
theorem original (field:∀Y,A.density x Y=stamped J (F x Y) (B x Y))
    (seen:WilsonOriginalAlternativeStamped.Heard C N p k J A F B)
    (quiet:∀Y,(F x Y).part J.quiet=(W.eval Y:ℂ)):
    let D:=charge C (N:=N) J F B x s lower U
    let total:=held C N p (fun Y=>(F x Y).part s) lower U-
        held C N p (fun Y=>(W.eval Y:ℂ)*∏v∈s.val,B x Y v) lower U
    (∀l:List V,l.toFinset=s.val → l.Nodup → total=tally D l) ∧
    ∀fee:V→ℝ,(∀j∈s.val,∀X:Finset V,X⊆s.val → j∉X → ‖D j X‖ ≤ fee j) →
      ‖total‖ ≤ ∑j∈s.val,fee j:=by
  intro D total
  have all : live J s s.val=s:=by apply Subtype.ext;simp [live]
  have none : live J s ∅=J.quiet:=by apply Subtype.ext;simp [live,Census.quiet]
  have leading : amount C (N:=N) J F B x s lower U s.val=held C N p (fun Y=>(F x Y).part s) lower U:=by
    simp [amount,all]
  have last : amount C (N:=N) J F B x s lower U ∅=held C N p (fun Y=>(W.eval Y:ℂ)*∏v∈s.val,B x Y v) lower U:=by
    simp [amount,none,quiet]
  have tel (l:List V) (same:l.toFinset=s.val) (once:l.Nodup): total=tally D l:=by
    have used:∀v∈l,v∈s.val:=fun v hv=>same ▸ List.mem_toFinset.mpr hv
    dsimp only [total]
    rw [←leading,←last]
    rw [←same]
    exact telescope _ D s.val (step C J A F B x s lower U field seen) l used once
  refine ⟨tel,?_⟩
  intro fee feePaid
  rw [tel s.val.toList (by simp) (Finset.nodup_toList _)]
  simpa using money D fee s.val feePaid s.val.toList (fun _ h=>Finset.mem_toList.mp h) (Finset.nodup_toList _)

end YM.Integration.WilsonOriginalAlternativeTelescope
