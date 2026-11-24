import YM.OPE.Trunk.Spine
import YM.OPE.Log.Peak
/-!
# Coherent placement snaps

Leader presence persists towards the finer segments. The *virtual* leader
for exactly one class through H (origin) may instead disappear. Thus a
point of a configuration is described by its offset from the parent leader
at the one step at which it becomes a leader. Vary these offsets independently
without changing smaller pair separations (including orientation of sign
step where used). Economizes on interpolation price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm
open Function Filter Finset Lattice RG Wilson Polar
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w:ℕ}
variable (Q)
def chiefAt (H:ℕ)(t:ℕ)(i:I) : Prop:= ¬ Q.pinned H i t ∧ Q.chief i t=i
lemma chief_old (h:Q.chiefAt H t i)(he:t ≤ u) : Q.chiefAt H u i:= ⟨fun h'=>h.1 (Q.pinSame h' he (Q.yes ..)),Q.leader_stays (t:=t) (⟨i,h.2⟩) he⟩
lemma chiefPinning (h: Q.phase t i j) : Q.pinned H i t ↔ Q.pinned H j t := ⟨fun he=>Q.pinSame he le_rfl h, fun he=>Q.pinSame he le_rfl (Q.swap h)⟩
lemma continue_leader (h:¬ Q.pinned H i t): Q.chiefAt H t (Q.chief i t):= ⟨fun he=> h ((Q.chiefPinning (Q.matchs i t)).mpr he), (Q.ticket i t).property⟩
lemma chief_off (H:ℕ)(i:I): ¬Q.chiefAt H 0 i:= fun h=> h.1 (Q.pinned_init _)
def localTime (H:ℕ)(i:I):ℕ:= let p t:= Q.chiefAt H (t+1) i; if h:∃ t,p t then Nat.find h else 0
local notation "t'"=> Q.localTime H
variable (hQ:H ≤ Q.age Q.star)
include hQ
lemma timeBy (i:I): Q.chiefAt H (t' i+1) i∧ ∀ t,Q.chiefAt H (t+1) i → t' i ≤ t:=by
    let p(t):=Q.chiefAt H (t+1) i; have h:∃ t,p t:= ⟨Q.age i, ⟨fun hp =>Nat.lt_succ_self _|>.not_ge (Q.pinAge hp hQ), Q.end_piece (Nat.lt_succ_self _)⟩⟩; rw [show t' i = Nat.find h from dif_pos h]; exact ⟨Nat.find_spec h,fun t=>Nat.find_min' h⟩
lemma clocked : Q.chiefAt H t i ↔ t' i < t := by cases t with | zero => exact ⟨fun h=> (Q.chief_off H i h).elim, fun h=> (Nat.not_lt_zero _ h).elim⟩ | succ t=> exact ⟨fun ht=>Nat.lt_succ_of_le ((Q.timeBy hQ i).2 t ht), fun ht=> Q.chief_old (Q.timeBy hQ _).1 (by omega)⟩
lemma timeBirth (i:I): t' i ≤ Q.age i:= (Q.timeBy hQ i).2 _ ⟨fun h=> Nat.lt_succ_self _|>.not_ge (Q.pinAge h hQ), Q.end_piece (Nat.lt_succ_self _)⟩
-- forks between roles. Pinning only allowed on spine
lemma debut (h:Q.chiefAt H (t+1) i)(he:¬Q.chiefAt H t i): t' i=t:= by rw [Q.clocked hQ] at h he; omega
lemma leadMom (h:¬Q.pinned H i t) : t' (Q.chief i t) < t:= (Q.clocked hQ).mp (Q.continue_leader h)

variable {X:Type}
omit hQ
-- Movement class descriptor.Build birth delta data
def tracked (H:ℕ) (i j:I): Prop:= Q.phase (Q.localTime H i+1) i j
variable (H)
def point [Zero X] (x:I→X)(i:I)(t:ℕ): X:= if Q.pinned H i t then 0 else x (Q.chief i t)
def stroke [Sub X][Zero X] (x:I→X)(i:I): X:=x i-Q.point H x i (t' i)
def reaches [Zero X](x:X)(i j:I): X:= if Q.tracked H i j then x else 0
variable {H}
lemma lead_eq [Zero X] (h: Q.phase t i j)(x:I→X) : Q.point H x i t=Q.point H x j t:=by unfold point; simp [Q.chiefPinning h,Q.chiefFor h]
lemma lead_at [Zero X] (h: Q.chiefAt H t i)(x : I→X): Q.point H x i t=x i:=by unfold point; rw [if_neg h.1,h.2]
lemma lead_zero [Zero X](h:Q.pinned H i t)(x:I→X): Q.point H x i t=0:= if_pos h
lemma funds [Zero X][Sub X] (x:I→X)(i:I) (h:Q.pinned H i (t' i)) : Q.stroke H x i=x i-0:=by unfold stroke; rw [lead_zero Q h]
lemma track_finer (h: Q.phase t i j)(he: t' k < t) : Q.tracked H k i ↔ Q.tracked H k j:=⟨fun h'=>Q.conj h' (Q.phase_low h he), fun h'=> Q.conj h' (Q.phase_low (Q.swap h) he)⟩
lemma follow_finer [Zero X](x:X)(h: Q.phase t i j)(he:t' k < t) : Q.reaches H x k i=Q.reaches H x k j:=by unfold reaches; simp only [Q.track_finer h he]
include hQ
lemma not_leading (h:t' i ≤ t' j) (he : i≠ j) : ¬ Q.tracked H j i:=by
    intro hp; have hh : Q.chiefAt H (t' j+1) i:= (Q.clocked hQ).mpr (by omega); have ht := Q.chiefFor (show Q.phase _ j i from hp); exact he (hh.2.symm.trans (ht.symm.trans (Q.timeBy hQ j|>.1.2)))
lemma trackingPoint [Zero X](i j:I)(x:X)(t:ℕ) : Q.point H (Q.reaches H x i) j t= if t' i<t then Q.reaches H x i j else 0:=by
    by_cases hj: Q.pinned H j t
    · rw [Q.lead_zero hj]; split ; next h=>
         refine Eq.symm (if_neg (show ¬Q.tracked H i j from ?_)); intro ht; have he:t' i+1 ≤ t:=(by omega); exact (Q.timeBy hQ i).1.1 (Q.pinSame hj he (Q.swap ht))
      rfl
    rw [point,if_neg hj]; by_cases h:t' i<t
    · rw [if_pos h]; exact Q.follow_finer x (Q.swap (Q.matchs ..)) h
    rw [if_neg h]; have hv:= Q.leadMom hQ hj; exact if_neg (Q.not_leading hQ (by omega) (by intro he; rw [he] at hv; exact h hv))
-- shift sum affine.
omit hQ
variable [AddCommGroup X]
def moveElig (Q:Rhythm I)(H:ℕ)(x:I→X)(z:I→X) (j:I): X:= x j+ ∑ i, Q.reaches H (z i) i j
variable (x y:I→X)
lemma pointSum (H:ℕ) (i:I)(t:ℕ) (v:I→ I → X): Q.point H (fun j=> ∑ a:I,v a j) i t= ∑ j,Q.point H (v j) i t:=by by_cases hi:Q.pinned H i t <;> simp [point,hi]
lemma pointAdd (H:ℕ)(i:I)(t:ℕ): Q.point H (fun i=>x i+y i) i t=Q.point H x i t+ Q.point H y i t:=by by_cases hi: Q.pinned H i t<;> simp [point,hi]
local notation "f'" => Q.moveElig H x y
include hQ
lemma stroke_move (i:I) : Q.stroke H (f') i= Q.stroke H x i+y i:=by
    let t:= t' i; let q j:= Q.reaches H (y j) j i; have he(j:I) (h:i≠j) : Q.point H (Q.reaches H (y j) j) i t= q j:=by
        rw [Q.trackingPoint hQ]; split; next h=> rfl
        next ht=> exact (show q j=0 from if_neg (Q.not_leading hQ (le_of_not_gt ht) h)).symm
    have hk:q i=y i:= if_pos (show Q.tracked H i i from Q.yes ..); unfold stroke moveElig; rw [Q.pointAdd, Q.pointSum]; change x i+(∑ j,q j)-(Q.point H x i t+ ∑ j,Q.point H (Q.reaches H (y j) j) i t)=_
    have ht:=add_sum_erase univ q (mem_univ i); have hf:=sum_congr rfl (s₁:= univ.erase i) (f:=q) (fun j hj=> (he j (mem_erase.mp hj).1.symm).symm); rw [← add_sum_erase univ (fun j=> Q.point H (Q.reaches H (y j) j) i t) (mem_univ _), Q.trackingPoint hQ, if_neg (show ¬ t' i < t from lt_irrefl _),← ht,hf,hk]; abel
omit hQ
lemma no_move (H:ℕ) : Q.moveElig H x 0=x:=by funext i; simp [moveElig,reaches]
-- bound perturbations by actual geometric layer later
lemma local_change (h: Q.phase t i j) (k:I)(he:t' k<t) : Q.reaches H (x k) k i=Q.reaches H (x k) k j:= Q.follow_finer _ h he
include hQ
lemma root_affords (h:Q.pinned H i t)(he:t' k < t) (x:X): Q.reaches H x k i=0:=by rw [← show _ = Q.reaches H x k i from (Q.trackingPoint hQ k i x t).trans (if_pos he),Q.lead_zero h]
end YM.OPE.Log.Trunk.Rhythm
