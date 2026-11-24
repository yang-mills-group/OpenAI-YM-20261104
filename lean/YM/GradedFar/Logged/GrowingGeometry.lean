import YM.OPE.Trees.Regime

/-!
# The `PublicForkGeometry` generalization

Keep one *joint* chart including nn coordinates of every Far slot,
so can later test same in replacements. And any center `o`.
Adapt `Integration/WilsonPublicForkGeometry` proofs. In this folder
`Logged` use `r,t` for physical radii (some other letters used for ratio/clock).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Tree
open Function Finset Filter Set OPE OPE.Arboreal
open scoped Topology BigOperators Classical

inductive Node (I J:Type) where
  | base | child | far (i : J) | leaf (i:I)
  deriving DecidableEq,Fintype
open Node
variable {I J:Type}[Fintype I][Fintype J]
def frame (I J:Type) : Arboreal (Node I J) where
    root:=base
    zones:={base,child}
    parent:=fun| base| child| far _=>base | leaf _=>child
    depth:=fun| base=>0| child| far _=>1| leaf _=>2
    direct:=rfl
    inward u:=by cases u <;> simp
    step u ne:=by cases u <;> simp_all

def near (I J:Type)[Fintype I]: Finset (Node I J):= Finset.univ.map ⟨leaf,fun _ _ he=>Node.leaf.inj he⟩
def terminalS (I J:Type)[Fintype J]: Finset (Node I J):= Finset.univ.map ⟨far,fun _ _ he=>Node.far.inj he⟩
abbrev outer (I J:Type) [Fintype J] : Finset (Node I J) := insert child (terminalS I J)
@[simp] lemma near_mem (i:I) : leaf i∈ near I J := by simp [near]
@[simp] lemma terminal_mem (i:J) : far i∈ terminalS I J:= by simp [terminalS]

lemma middle : (frame I J).middle (frame I J).zones={child}:= by ext u; cases u <;> simp [Arboreal.middle,frame]
lemma empty_child : child ∉ terminalS I J:= by simp [terminalS]
lemma away : Disjoint (near I J) (terminalS I J) := Finset.disjoint_left.mpr (fun u hu hp => by cases u <;> simp_all [near,terminalS])
lemma leaves : (frame I J).leaves=near I J ∪ terminalS I J:= by
    ext u; cases u <;> simp [Arboreal.leaves,Arboreal.live,frame,near,terminalS]
lemma pruned : (frame I J).live ((frame I J).zones.erase child)=outer I J:= by
    ext u; cases u <;> simp [Arboreal.live,frame,outer,terminalS]

def position (r t:ℝ) (x:I→E4)(z:J→E4)(o:E4):Node I J→E4
 | base| child=>o
 | leaf i=>o+r • x i
 | far j=>o+t • z j
def radius (r t:ℝ) : Node I J→ℝ
 | base| far _=> t
 | child | leaf _=> r
omit [Fintype I] [Fintype J] in
private theorem terminal {a b:Node I J} (e:a∉(frame I J).zones)(anc:(frame I J).Anc a b):a=b := by
  by_contra h
  exact e (anc.proper (Ne.symm h))
omit [Fintype I] [Fintype J] in
private theorem branch {u:Node I J}(a:(frame I J).Anc child u):u=child ∨ ∃i,u=leaf i := by
  cases u with
  | base => exact (nomatch (a.excess))
  | child => exact Or.inl rfl
  | far i=>
    have n:=a.into (by intro e;cases e)
    exact (Nat.lt_irrefl 1 n).elim
  | leaf i => exact Or.inr ⟨i,rfl⟩
theorem incoming : (frame I J).inputs (frame I J).zones child=near I J := by
  ext u
  change (u∈(frame I J).leaves.filter ((frame I J).Anc child)) ↔ _
  rw [leaves,mem_filter]
  cases u with
  | base | child => simp [near,terminalS]
  | far i => simp [near]; intro impossible; rcases branch impossible with eq|⟨i,eq⟩ <;> cases eq
  | leaf i =>
    have he: (frame I J).Anc child (leaf i):=Anc.step (frame I J) (leaf i)
    simp [he]

set_option maxHeartbeats 500000 in
lemma actual {r t M δ:ℝ}{x:I→E4}{z:J→E4} (o:E4)
    (rp:0<r)(rt:r≤t)(mn:0≤M)(dn:0≤δ)
    (nx:∀ i,‖x i‖≤M)(nz:∀ i,‖z i‖≤M)(away:∀ i,2*δ≤‖z i‖)
    (separation:∀i j,i≠j→δ≤‖x i-x j‖)
    (outer_sep:∀i j,i≠j→δ≤‖z i-z j‖)(gap:r*M≤ t*δ): (frame I J).Convoy M δ (radius r t) (position r t x z o) := by
  have tp:=rp.trans_le rt
  have small (i:I):‖r • x i‖≤M*r:=by rw [norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact nx i
  have big (i:J):‖t • z i‖≤M*t:=by rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr;exact nz i
  have farAway (u:Node I J) (a:(frame I J).Anc child u) (i:J) :
      δ*t≤‖position r t x z o u-position r t x z o (far i)‖:=by
    have low:‖position r t x z o u-o‖≤t*δ:=by
      rcases branch a with rfl|⟨i,rfl⟩
      · simpa [position] using mul_nonneg tp.le dn
      rw [position,add_sub_cancel_left]; exact (small i).trans (mul_comm r M ▸ gap)
    have high:2*(t*δ)≤‖position r t x z o (far i)-o‖:=by
      change _≤‖o+t • z i-o‖
      rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg tp.le]
      linarith only [mul_le_mul_of_nonneg_left (away i) tp.le]
    have h:= norm_sub_norm_le (position r t x z o (far i)-o) (position r t x z o u-o)
    rw [sub_sub_sub_cancel_right,norm_sub_rev _ (position r t x z o u)] at h
    linarith only [h,low,high,mul_comm t δ]
  constructor
  · constructor
    · intro u hu;cases u <;> simp_all [frame,radius]
    · intro u hu;cases u <;> simp_all [frame,radius]
  · intro u;cases u <;> simp [frame,position,radius,small,big,mul_nonneg mn tp.le]
  · intro u j k fork
    have live: u=base ∨ u=child:=by simpa [frame] using fork.inner
    rcases fork with ⟨a,ha,b,hb,ne,aj,bk⟩
    rcases live with rfl|rfl
    · have kids {w:Node I J} (h:w∈(frame I J).kids base) : w=child ∨ ∃i,w=far i := by
        cases w <;> simp_all [Arboreal.kids,frame]
      rcases kids ha with rfl|⟨i,rfl⟩ <;> rcases kids hb with rfl|⟨i',rfl⟩
      · exact (ne rfl).elim
      · rw [←terminal (by simp [frame]) bk]
        exact farAway j aj i'
      · rw [←terminal (by simp [frame]) aj,norm_sub_rev]
        exact farAway k bk i
      · rw [←terminal (by simp [frame]) aj,←terminal (by simp [frame]) bk]
        change δ*t≤‖o+t • z i-(o+t • z i')‖; rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg tp.le,mul_comm]
        exact mul_le_mul_of_nonneg_left (outer_sep i i' (fun eq=>ne (congrArg far eq))) tp.le
    · have kids {w:Node I J} (h:w∈(frame I J).kids child) : ∃i,w=leaf i := by
        cases w <;> simp_all [Arboreal.kids,frame]
      obtain ⟨i,rfl⟩:=kids ha
      obtain ⟨l,rfl⟩:=kids hb
      rw [←terminal (by simp [frame]) aj,←terminal (by simp [frame]) bk]
      change δ*r≤‖o+r • x i-(o+r • x l)‖
      rw [add_sub_add_left_eq_sub, ←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
      exact mul_le_mul_of_nonneg_left (separation i l (fun eq=>ne (congrArg leaf eq))) rp.le
end YM.OPE.Logged.Tree
