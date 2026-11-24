import YM.OPE.Trees.Regime

/-!
# HorizonFork: adapt PublicFork{Geometry,Rooms,Stage,Ordinary} to two-zone inputs

Here both I, J any Fintype. Also arbitrary center, uniformly all estimates retain it.
The second zone is literally centered at the same point, with a different radius;
not determining Viewer after that scale switch.

We adapt proof and often directly adapt Lean code from
`YM/Integration/WilsonPublicFork{Geometry,Rooms,Stage,Ordinary}.lean`.
In these modules also include some small standalone/original-reduced supplier proofs from that
project chain (noted beside each). This reduces audited **import closure**; does not reduce objects
to standalone surrogates -- they still typecheck on the original sources.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Function Finset Filter Set OPE OPE.Arboreal
open scoped Topology BigOperators Classical

inductive Node (I J:Type) where
  | base | child | far (j:J) | leaf (i:I)
  deriving DecidableEq, Fintype
open Node
variable {I J:Type} [Fintype I] [Fintype J]

def tree (I J:Type) : Arboreal (Node I J) where
  root := base
  zones := {base,child}
  parent := fun | base | child | far _ => base | leaf _ => child
  depth := fun | base => 0 | child | far _ => 1 | leaf _ => 2
  direct := rfl
  inward u := by cases u <;> simp
  step u ne := by cases u <;> simp_all

def near (I J:Type) [Fintype I] : Finset (Node I J) := Finset.univ.map ⟨leaf,fun _ _ e=>Node.leaf.inj e⟩
def broad (I J:Type) [Fintype J] : Finset (Node I J) := Finset.univ.map ⟨far,fun _ _ e=>Node.far.inj e⟩
def outer (I J:Type) [Fintype J] : Finset (Node I J) := insert child (broad I J)

omit [Fintype I] [Fintype J] in
theorem middle : (tree I J).middle (tree I J).zones={child} := by ext u; cases u <;> simp [Arboreal.middle,tree]
theorem leaves : (tree I J).leaves=near I J ∪ broad I J := by
  ext u; cases u <;> simp [Arboreal.leaves,Arboreal.live,tree,near,broad]
theorem pruned (de: DecidableEq (Node I J)) : (tree I J).live (@Finset.erase _ de (tree I J).zones child)=outer I J := by
  ext u;cases u <;> simp [Arboreal.live,tree,outer,broad]

def position (o:E4)(r t:ℝ)(x:I→E4)(z:J→E4):Node I J→E4
  | base | child => o
  | far j => o + t • z j
  | leaf i => o + r • x i

def radius (r t:ℝ):Node I J→ℝ
  | base | far _ => t
  | child | leaf _ => r

omit [Fintype I] [Fintype J] in
private theorem terminal {a b:Node I J} (e:a∉(tree I J).zones)(anc:(tree I J).Anc a b):a=b := by
  by_contra h
  exact e (anc.proper (Ne.symm h))

omit [Fintype I] [Fintype J] in
private theorem branch {u:Node I J}(a:(tree I J).Anc child u):u=child ∨ ∃i,u=leaf i := by
  cases u with
  | base => exact (nomatch (a.excess))
  | child => exact Or.inl rfl
  | far _ =>
    have n:=a.into (by intro e;cases e)
    exact (Nat.lt_irrefl 1 n).elim
  | leaf i => exact Or.inr ⟨i,rfl⟩

theorem incoming : (tree I J).inputs (tree I J).zones child=near I J := by
  ext u; change u∈(tree I J).leaves.filter ((tree I J).Anc child) ↔ _
  rw [leaves,mem_filter]
  cases u with
  | base | child => simp [near,broad]
  | far j => simp [near,broad]; intro impossible; rcases branch impossible with eq|⟨i,eq⟩ <;> cases eq
  | leaf i =>
    have he: (tree I J).Anc child (leaf i):=Anc.step (tree I J) (leaf i)
    simp [near,broad,he]

structure Setting (M δ : ℝ) (x:I→E4) (z:J→E4) : Prop where
  xhome : ∀ i,‖x i‖≤M
  zhome : ∀ i,‖z i‖≤M
  xclear : ∀i j,i≠j→δ≤‖x i-x j‖
  zclear : ∀i j,i≠j→δ≤‖z i-z j‖
  away : ∀ i,2*δ≤‖z i‖
section
variable {r t M δ:ℝ}{x:I→E4}{z:J→E4} (o : E4)
def move (o:E4) (r:ℝ) (x:I → E4) (i:I) := o+r • x i
omit [Fintype I] [Fintype J] in
lemma farAway (rp:0<r) (rt:r≤t) (dn:0≤δ) (hx:Setting M δ x z)
    (gap:r*M≤t*δ) (u:Node I J) (a:(tree I J).Anc child u) (j:J):
    δ*t≤‖position o r t x z u-position o r t x z (far j)‖:=by
  have low:‖position o r t x z u - o‖≤t*δ:=by
    rcases branch a with rfl|⟨i,rfl⟩
    · simpa [position] using mul_nonneg (rp.le.trans rt) dn
    · rw [position, add_sub_cancel_left,norm_smul,Real.norm_of_nonneg rp.le]; exact
        (mul_le_mul_of_nonneg_left (hx.xhome i) rp.le).trans gap
  have high:2*(t*δ)≤‖position o r t x z (far j) - o‖:=by
    rw [position,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (rp.le.trans rt)]
    linarith only [mul_le_mul_of_nonneg_left (hx.away j) (rp.le.trans rt)]
  set p := position o r t x z (far j); set q := position o r t x z u
  have hu := norm_sub_norm_le (p-o) (q-o)
  rw [sub_sub_sub_cancel_right] at hu
  linarith only [norm_sub_rev p q, hu,low,high,mul_comm t δ]

set_option maxHeartbeats 600000 in
theorem actual (rp:0<r) (rt:r≤t) (mn:0≤M) (dn:0≤δ) (hx:Setting M δ x z)
    (gap:r*M≤t*δ) : (tree I J).Convoy M δ (radius r t) (position o r t x z) := by
  have tp:=rp.trans_le rt
  have small (i:I):‖r • x i‖≤M*r:=by rw [norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact hx.xhome i
  have big (j:J):‖t • z j‖≤M*t:=by rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr;exact hx.zhome j
  constructor
  · constructor
    · intro u hu;cases u <;> simp_all [tree,radius]
    · intro u hu;cases u <;> simp_all [tree,radius]
  · intro u;cases u <;> simp only [tree,position,radius,add_sub_cancel_left,sub_self,norm_zero]
    · exact mul_nonneg mn tp.le
    · exact mul_nonneg mn tp.le
    · exact big _
    · exact small _
  · intro u j k fork
    have live: u=base ∨ u=child:=by simpa [tree] using fork.inner
    rcases fork with ⟨a,ha,b,hb,ne,aj,bk⟩
    rcases live with rfl|rfl
    · have kids {w:Node I J} (h:w∈(tree I J).kids base) : w=child ∨ ∃ j,w=far j := by
        cases w <;> simp_all [Arboreal.kids,tree]
      rcases kids ha with rfl|⟨i,rfl⟩ <;> rcases kids hb with rfl|⟨l,rfl⟩
      · exact (ne rfl).elim
      · rw [←terminal (by simp [tree]) bk]
        exact farAway o rp rt dn hx gap _ aj l
      · rw [←terminal (by simp [tree]) aj,norm_sub_rev]
        exact farAway o rp rt dn hx gap _ bk i
      · rw [←terminal (by simp [tree]) aj,←terminal (by simp [tree]) bk]
        rw [position,position,add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_of_nonneg tp.le,mul_comm]
        exact mul_le_mul_of_nonneg_left (hx.zclear i l (fun eq=>ne (congrArg far eq))) tp.le
    · have kids {w:Node I J} (h:w∈(tree I J).kids child) : ∃i,w=leaf i := by
        cases w <;> simp_all [Arboreal.kids,tree]
      obtain ⟨i,rfl⟩:=kids ha
      obtain ⟨l,rfl⟩:=kids hb
      rw [←terminal (by simp [tree]) aj,←terminal (by simp [tree]) bk]
      rw [position,position,add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
      exact mul_le_mul_of_nonneg_left (hx.xclear i l (fun eq=>ne (congrArg leaf eq))) rp.le

omit [Fintype I] [Fintype J] in
lemma distinct {x : I→E4} (hp : 0<r) (hd : 0<δ) (hx:∀i j,i≠j→δ≤‖x i-x j‖) : Injective (move o r x) := by
  intro i j h; by_contra ne; have hh:=hx i j ne
  change o+_ = o+_ at h
  rw [smul_right_injective E4 hp.ne' (add_left_cancel h),sub_self,norm_zero] at hh; linarith
lemma full_layout (hx:Setting M δ x z) (hd:0<δ)(hp:0<r)(ht:r≤t) (gap:r*M≤t*δ) :
    Injective (beside (move o r x) (move o t z)) := by
  refine beside_distinct.mpr ⟨distinct o hp hd hx.xclear, distinct o (hp.trans_le ht) hd hx.zclear, fun i j h=>?_⟩
  have hP := farAway o hp ht hd.le hx gap (leaf i) (Anc.step ..) j
  change _ ≤ ‖move o r x i-move o t z j‖ at hP
  rw [h,sub_self,norm_zero] at hP; exact (mul_pos hd (hp.trans_le ht)).not_ge hP
lemma center_layout (tp:0<t) (hd:0<δ) (hz:∀ i,2*δ≤‖z i‖) (hsep:∀i j,i≠j→δ≤‖z i-z j‖) :
    Injective (beside (sole o) (move o t z)) := by
  refine beside_distinct.mpr ⟨injective_of_subsingleton _, distinct o tp hd hsep,?_⟩
  intro _ i h; change o = o+_ at h; have he:=smul_eq_zero.mp (left_eq_add.mp h)
  specialize hz i; rw [he.resolve_left tp.ne',norm_zero] at hz; linarith

omit [Fintype J] in
lemma leafRoom (rp:0<r) (nx:∀ i,‖x i‖≤M) (nc:∀i j,i≠j→δ≤‖x i-x j‖):
    WithinRoom r M δ (Arboreal.crop (position o r t x z) (near I J)) o := by
  constructor
  · rintro ⟨u,hu⟩; obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp hu; change ‖o+r • x i - o‖ ≤ M*r
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact nx i
  · rintro ⟨u,hu⟩ ⟨v,hv⟩ ne; obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp hu; obtain ⟨j,_,rfl⟩:= Finset.mem_map.mp hv
    change δ*r≤‖(o+r • x i)-(o+r • x j)‖; rw [add_sub_add_left_eq_sub,
      ←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (nc i j (fun he=>ne (Subtype.ext (congrArg leaf he)))) rp.le
omit [Fintype I] in
lemma outerRoom (tp:0<t) (mn:0≤M) (dp:0≤δ) (nx:∀ j,‖z j‖≤M) (away:∀ j,2*δ≤‖z j‖)
    (nc:∀i j,i≠j→δ≤‖z i-z j‖):
    WithinRoom t M δ (Arboreal.crop (position o r t x z) (outer I J)) o := by
  have hu (i:J): δ*t≤‖t • z i‖:=by
    rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm]; gcongr; linarith [away i]
  constructor
  · rintro ⟨u,hm⟩; rcases Finset.mem_insert.mp hm with he|ho
    · subst u; change ‖o-o‖ ≤ _; rw [sub_self,norm_zero];exact mul_nonneg mn tp.le
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ho; change ‖o+t • z i-o‖ ≤ _
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg tp.le,mul_comm]; gcongr;exact nx i
  · rintro ⟨u,hm⟩ ⟨v,hv⟩ ne; rcases Finset.mem_insert.mp hm with he|ho <;> rcases Finset.mem_insert.mp hv with hl|hv
    · exact (ne (Subtype.ext (he.trans hl.symm))).elim
    · subst u; obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp hv; change _ ≤ ‖o-(o+t • z i)‖; rw [norm_sub_rev,add_sub_cancel_left]; exact hu i
    · subst v; obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp ho; change _ ≤ ‖o+t • z i-o‖; rw [add_sub_cancel_left]; exact hu i
    obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp ho; obtain ⟨j,_,rfl⟩:= Finset.mem_map.mp hv
    change δ*t≤‖(o+t • z i)-(o+t • z j)‖; rw [add_sub_add_left_eq_sub,
      ←smul_sub,norm_smul,Real.norm_of_nonneg tp.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (nc i j (fun he=>ne (Subtype.ext (congrArg far he)))) tp.le
end
end YM.Integration.GradedFar.Fork
