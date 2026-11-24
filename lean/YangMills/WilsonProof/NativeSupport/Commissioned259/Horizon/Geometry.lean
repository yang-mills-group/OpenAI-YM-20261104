import YM.OPE.Logarithmic
/-!
# For G.4, generalize Geometry,
Rooms,Stage,Ordinary from YM/Integration/WilsonPublicFork on this SAME tree with arbitrary
finite number of distant fields, all viewed by the chosen phase, simultaneously uniform.

Here and in Horizon/. adapt/pin many existing Lean proofs, reusing the proof steps &
original purchases, never assumed extended to these arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Finset Filter Set Arboreal
open scoped Topology BigOperators Classical

abbrev atPosition {I : Type*} (o:E4) (r : ℝ) (x:I→E4) (i:I) := o+r • x i
-- nearest and distant: prices entirely uniform in this geometry.
structure Ready {I J : Type*} (r t M δ : ℝ) (x:I→E4) (z:J→E4) : Prop where
  length : 0 < r
  adj : r ≤ t
  close (i : I) : ‖x i‖≤ M
  reaches (j : J) : ‖z j‖ ≤ M
  away (j : J) : 2*δ ≤ ‖z j‖
  separation (i i' : I) : i≠i' → δ ≤ ‖x i-x i'‖
  separated (j j' : J) : j≠j' → δ ≤ ‖z j-z j'‖
  gap : r*M ≤ t*δ
inductive Node (I J : Type) where
  | base | child | far (j:J) | leaf (i:I)
  deriving DecidableEq, Fintype
open Node
variable {I J : Type} [Fintype I] [Fintype J]
local notation "N" => Node I J

def frame (I J : Type) : Arboreal (Node I J) where
  root := base
  zones := {base,child}
  parent := fun | base | child | far _ => base | leaf _ => child
  depth := fun | base => 0 | child | far _ => 1 | leaf _ => 2
  direct := rfl
  inward u := by cases u <;> simp
  step u ne := by cases u <;> simp_all

def near (I J : Type) [Fintype I] : Finset (Node I J) := Finset.univ.map ⟨leaf,fun _ _ e=>Node.leaf.inj e⟩
def rim (I J : Type) [Fintype J] : Finset (Node I J) := Finset.univ.map ⟨far,fun _ _ e=>Node.far.inj e⟩
def outer (I J : Type) [Fintype J] : Finset (Node I J) := insert child (rim I J)

@[simp] theorem near_mem (i:I) : leaf i ∈ near I J := by simp [near]
@[simp] theorem rim_mem (j:J) : far j ∈ rim I J := by simp [rim]
omit [Fintype I] [Fintype J] in
theorem middle : (frame I J).middle (frame I J).zones = {child} := by ext u; cases u <;> simp [Arboreal.middle,frame]
theorem leaves : (frame I J).leaves=near I J ∪ rim I J := by
  ext u; cases u <;> simp [Arboreal.leaves,Arboreal.live,frame,near,rim]
theorem pruned : (frame I J).live ((frame I J).zones.erase child)=outer I J := by
  ext u;cases u <;> simp [Arboreal.live,frame,outer,rim]

def sites (o:E4)(r t:ℝ)(x:I→E4)(z:J→E4): N → E4
  | base | child => o
  | far j => atPosition o t z j
  | leaf i => atPosition o r x i

def radius (r t:ℝ):Node I J→ℝ
  | base | far _ => t
  | child | leaf _ => r
omit [Fintype I] [Fintype J] in
private theorem terminal {a b: Node I J} (e:a∉(frame I J).zones)(anc:(frame I J).Anc a b):a=b := by
  by_contra h
  exact e (anc.proper (Ne.symm h))
omit [Fintype I] [Fintype J] in
private theorem branch {u:Node I J}(a:(frame I J).Anc child u):u=child ∨ ∃i,u=leaf i := by
  cases u with
  | base => exact (nomatch (a.excess))
  | child => exact Or.inl rfl
  | far j =>
    have n:=a.into (by intro e;cases e); exact (Nat.lt_irrefl 1 n).elim
  | leaf i => exact Or.inr ⟨i,rfl⟩
theorem incoming : (frame I J).inputs (frame I J).zones child=near I J := by
  ext u
  change (u∈(frame I J).leaves.filter ((frame I J).Anc child)) ↔ _
  rw [leaves,mem_filter]
  cases u with
  | base | child => simp [near,rim]
  | far j => simp [near,rim]; intro impossible; rcases branch impossible with eq|⟨i,eq⟩ <;> cases eq
  | leaf i => simp; exact Anc.step (frame I J) (leaf i)

section Position
variable {r t M δ : ℝ} {x : I→E4} {z:J→E4} (o:E4)
omit [Fintype I] in
lemma only_room (nr : 0 < r) (nx:∀ i, ‖x i‖ ≤ M) (sep:∀ i j, i≠j→ δ ≤ ‖x i-x j‖) :
    WithinRoom r M δ (atPosition o r x) o := by
  constructor
  · intro i; simp only [atPosition, add_sub_cancel_left,norm_smul,Real.norm_of_nonneg nr.le]; exact ((mul_le_mul_of_nonneg_left (nx i) nr.le).trans_eq (mul_comm ..))
  intro i j h; simp only [atPosition, add_sub_add_left_eq_sub, ← smul_sub,norm_smul,Real.norm_of_nonneg nr.le]
  rw [mul_comm]; exact mul_le_mul_of_nonneg_left (sep i j h) nr.le
variable (h : Ready r t M δ x z)
include h
omit [Fintype I] [Fintype J] in
lemma middle_far (δp:0≤δ) (i : Node I J) (a:(frame I J).Anc child i) (j:J) : δ*t ≤ ‖sites o r t x z i-sites o r t x z (far j)‖ := by
  have ht := h.length.trans_le h.adj
  have low : ‖sites o r t x z i-o‖ ≤ t*δ := by
    rcases branch a with rfl|⟨i,rfl⟩
    · simp [sites, mul_nonneg ht.le δp]
    exact le_trans ((only_room o h.length h.close h.separation).1 i) ((mul_comm _ _).le.trans h.gap)
  have e : ‖sites o r t x z (far j)-o‖=t*‖z j‖ := by change ‖o+t • z j-o‖=_; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.le]
  have A:= norm_sub_norm_le (sites o r t x z (far j)-o) (sites o r t x z i-o)
  rw [sub_sub_sub_cancel_right,e,norm_sub_rev (sites o r t x z (far j))] at A
  linarith only [low,A,mul_le_mul_of_nonneg_left (h.away j) ht.le, mul_comm δ t]

lemma profiles (dp:0<δ) : Function.Injective (beside (atPosition o r x) (atPosition o t z)) := by
  rw [beside_distinct]; have p:= only_room o h.length h.close h.separation; have ht := h.length.trans_le h.adj; have q := only_room o ht h.reaches h.separated
  refine ⟨?_,?_,?_⟩
  · intro i j e; by_contra ne; have v:=p.2 i j ne; rw [e,sub_self,norm_zero] at v; exact (mul_pos dp h.length).not_ge v
  · intro i j e; by_contra ne; have v:=q.2 i j ne; rw [e,sub_self,norm_zero] at v; exact (mul_pos dp ht).not_ge v
  intro i j e; have hp := middle_far o h dp.le (leaf i) (Anc.step (frame I J) (leaf i)) j
  change δ*t≤‖atPosition o r x i-atPosition o t z j‖ at hp; rw [e,sub_self,norm_zero] at hp; exact (mul_pos dp ht).not_ge hp
lemma center_profiles (dp:0<δ) : Function.Injective (beside (sole o) (atPosition o t z)) := by
  rw [beside_distinct]; refine ⟨injective_of_subsingleton _,(beside_distinct.mp (profiles o h dp)).2.1,?_⟩; intro i j e
  have hp := middle_far o h dp.le child (.same ..) j; change δ*t ≤ ‖o-atPosition o t z j‖ at hp; rw [(show atPosition o t z j=o from e.symm),sub_self,norm_zero] at hp
  exact (mul_pos dp (h.length.trans_le h.adj)).not_ge hp

theorem convoy (mn:0≤M)(dp:0≤δ) : (frame I J).Convoy M δ (radius r t) (sites o r t x z) := by
  obtain ht := h.length.trans_le h.adj
  have near₀ := only_room o h.length h.close h.separation; have outer₀ := only_room o ht h.reaches h.separated
  constructor
  · constructor
    · intro i hi; cases i <;> simp_all [frame,radius,h.length,h.adj]
    · intro i hi; cases i <;> simp_all [frame,radius,h.length,h.adj]
  · intro u; cases u with
    | base | child => simp [frame,sites,radius,mul_nonneg mn ht.le]
    | leaf i => exact near₀.1 i
    | far j=> exact outer₀.1 j
  · intro u i j fork
    have live: u=base ∨ u=child:=by simpa [frame] using fork.inner
    rcases fork with ⟨a,ha,b,hb,ne,ai,bj⟩; rcases live with rfl|rfl
    · have kids {w:Node I J} (h:w∈(frame I J).kids base) : w=child ∨ ∃ j,w=far j := by
        cases w <;> simp_all [Arboreal.kids,frame]
      rcases kids ha with rfl|⟨l,rfl⟩ <;> rcases kids hb with rfl|⟨k,rfl⟩
      · exact (ne rfl).elim
      · rw [←terminal (by simp [frame]) bj]; exact middle_far o h dp _ ai k
      · rw [←terminal (by simp [frame]) ai,norm_sub_rev]; exact middle_far o h dp _ bj l
      · rw [←terminal (by simp [frame]) ai,←terminal (by simp [frame]) bj]
        exact outer₀.2 _ _ (fun he=>ne (congrArg far he))
    have kids {w:Node I J} (h:w∈(frame I J).kids child) : ∃i,w=leaf i := by
      cases w <;> simp_all [Arboreal.kids,frame]
    obtain ⟨l,rfl⟩:=kids ha; obtain ⟨k,rfl⟩:=kids hb
    rw [←terminal (by simp [frame]) ai,←terminal (by simp [frame]) bj]
    exact near₀.2 _ _ (fun he=>ne (congrArg leaf he))
end Position
end YM.OPE.Flash259HorizonFork
