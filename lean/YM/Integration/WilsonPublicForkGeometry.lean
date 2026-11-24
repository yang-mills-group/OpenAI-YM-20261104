import YM.OPE.Logarithmic

/-! A two-radius tree with any finite near roster and one distant occupied
leaf. Every leaf carries its own actual position and its own engineering cost. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkGeometry
open Function Finset Filter Set OPE OPE.Arboreal
open scoped Topology BigOperators Classical

inductive Node (I:Type) where
  | base | child | far | leaf (i:I)
  deriving DecidableEq, Fintype
open Node
variable {I:Type} [Fintype I]

def frame (I:Type) : Arboreal (Node I) where
  root := base
  zones := {base,child}
  parent := fun | base | child | far => base | leaf _ => child
  depth := fun | base => 0 | child | far => 1 | leaf _ => 2
  direct := rfl
  inward u := by cases u <;> simp
  step u ne := by cases u <;> simp_all

def near (I:Type) [Fintype I] : Finset (Node I) := Finset.univ.map ⟨leaf,fun _ _ e=>Node.leaf.inj e⟩
def outer (I:Type) : Finset (Node I) := {child,far}

@[simp] theorem near_mem (i:I) : leaf i∈near I := by simp [near]
@[simp] theorem other_near : (base:Node I)∉near I ∧ (child:Node I)∉near I ∧ (far:Node I)∉near I := by simp [near]

omit [Fintype I] in
theorem middle : (frame I).middle (frame I).zones={child} := by ext u; cases u <;> simp [Arboreal.middle,frame]
theorem leaves : (frame I).leaves=insert far (near I) := by
  ext u; cases u <;> simp [Arboreal.leaves,Arboreal.live,frame,near]
theorem pruned : (frame I).live ((frame I).zones.erase child)=outer I := by
  ext u;cases u <;> simp [Arboreal.live,frame,outer]

def position (r t:ℝ)(x:I→E4)(z:E4):Node I→E4
  | base | child => 0
  | far => t • z
  | leaf i => r • x i

def radius (r t:ℝ):Node I→ℝ
  | base | far => t
  | child | leaf _ => r

omit [Fintype I] in
private theorem terminal {a b:Node I} (e:a∉(frame I).zones)(anc:(frame I).Anc a b):a=b := by
  by_contra h
  exact e (anc.proper (Ne.symm h))

omit [Fintype I] in
private theorem branch {u:Node I}(a:(frame I).Anc child u):u=child ∨ ∃i,u=leaf i := by
  cases u with
  | base => exact (nomatch (a.excess))
  | child => exact Or.inl rfl
  | far =>
    have n:=a.into (by intro e;cases e)
    exact (Nat.lt_irrefl 1 n).elim
  | leaf i => exact Or.inr ⟨i,rfl⟩

theorem incoming : (frame I).inputs (frame I).zones child=near I := by
  ext u
  change (u∈(frame I).leaves.filter ((frame I).Anc child)) ↔ _
  rw [leaves,mem_filter]
  cases u with
  | base | child => simp [near]
  | far => simp [near]; intro impossible; rcases branch impossible with eq|⟨i,eq⟩ <;> cases eq
  | leaf i =>
    have he: (frame I).Anc child (leaf i):=Anc.step (frame I) (leaf i)
    simp [he]

theorem actual {r t M δ:ℝ}{x:I→E4}{z:E4}
    (rp:0<r) (rt:r≤t) (mn:0≤M) (dn:0≤δ)
    (nx:∀ i,‖x i‖≤M) (nz:‖z‖≤M) (away:2*δ≤‖z‖)
    (separation:∀i j,i≠j→δ≤‖x i-x j‖) (gap:r*M≤t*δ) :
    (frame I).Convoy M δ (radius r t) (position r t x z) := by
  have tp:=rp.trans_le rt
  have small (i:I):‖r • x i‖≤M*r:=by rw [norm_smul,Real.norm_of_nonneg rp.le,mul_comm];gcongr;exact nx i
  have big:‖t • z‖≤M*t:=by rw [norm_smul,Real.norm_of_nonneg tp.le,mul_comm];gcongr
  have farAway (u:Node I) (a:(frame I).Anc child u) :
      δ*t≤‖position r t x z u-position r t x z far‖:=by
    have low:‖position r t x z u‖≤t*δ:=by
      rcases branch a with rfl|⟨i,rfl⟩
      · simpa [position] using mul_nonneg tp.le dn
      · exact (small i).trans (mul_comm r M ▸ gap)
    have high:2*(t*δ)≤‖position r t x z far‖:=by
      change _≤‖t • z‖
      rw [norm_smul,Real.norm_of_nonneg tp.le]
      linarith only [mul_le_mul_of_nonneg_left away tp.le]
    linarith only [norm_sub_rev (position r t x z u) (position r t x z far),
      norm_sub_norm_le (position r t x z far) (position r t x z u),low,high,mul_comm t δ]
  constructor
  · constructor
    · intro u hu;cases u <;> simp_all [frame,radius]
    · intro u hu;cases u <;> simp_all [frame,radius]
  · intro u;cases u <;> simp [frame,position,radius,small,big,mul_nonneg mn tp.le]
  · intro u j k fork
    have live: u=base ∨ u=child:=by simpa [frame] using fork.inner
    rcases fork with ⟨a,ha,b,hb,ne,aj,bk⟩
    rcases live with rfl|rfl
    · have kids {w:Node I} (h:w∈(frame I).kids base) : w=child ∨ w=far := by
        cases w <;> simp_all [Arboreal.kids,frame]
      rcases kids ha with rfl|rfl <;> rcases kids hb with rfl|rfl
      · exact (ne rfl).elim
      · rw [←terminal (by simp [frame]) bk]
        exact farAway j aj
      · rw [←terminal (by simp [frame]) aj,norm_sub_rev]
        exact farAway k bk
      · exact (ne rfl).elim
    · have kids {w:Node I} (h:w∈(frame I).kids child) : ∃i,w=leaf i := by
        cases w <;> simp_all [Arboreal.kids,frame]
      obtain ⟨i,rfl⟩:=kids ha
      obtain ⟨l,rfl⟩:=kids hb
      rw [←terminal (by simp [frame]) aj,←terminal (by simp [frame]) bk]
      change δ*r≤‖r • x i-r • x l‖
      rw [←smul_sub,norm_smul,Real.norm_of_nonneg rp.le,mul_comm]
      exact mul_le_mul_of_nonneg_left (separation i l (fun eq=>ne (congrArg leaf eq))) rp.le
end YM.Integration.WilsonPublicForkGeometry
