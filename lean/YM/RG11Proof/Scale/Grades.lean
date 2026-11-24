import YM.RG11Proof.Scale.Beam
/-!
# Block (engineering grade) matrices

Because rows incoming, lower block allowed BEFORE separated scale laws.
`position` variant with H preserving grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Scale
open YM.RG11.Jets PowerSeries
open scoped BigOperators Classical

variable {R J:Type*}(w:J→ℕ)

def graded [Zero R](A:Square J R):Prop:=∀ {i j}, w i≠w j→ A i j=0

def isolate [Zero R](A:Square J R):Square J R:= Matrix.of fun i j=> if w i=w j then A i j else 0
namespace graded
variable {w}
variable {A B:Square J R}

theorem isIsolated [Zero R](A:Square J R):graded w (isolate w A):=fun he=>by simp [isolate, he]

theorem invariant [Zero R](h:graded w A):isolate w A=A:=Matrix.ext fun i j=>by
   by_cases H:w i=w j
   · simp [isolate,H]
   simp [isolate,H,h H]

protected theorem zero [Zero R]: graded w (0:Square J R):=fun _=>rfl

protected theorem one [DecidableEq J][One R][Zero R]:graded w (1:Square J R):=fun he=>Matrix.one_apply_ne (fun hh=> he (congrArg w hh))

protected theorem add [AddZeroClass R](h:graded w A)(k:graded w B): graded w (A+B):= fun H=>by rw [Matrix.add_apply,h H,k H,add_zero]

protected theorem sub [AddGroup R](h:graded w A)(k:graded w B): graded w (A-B):= fun H=>by rw [Matrix.sub_apply,h H,k H,sub_self]

protected theorem mul [Fintype J][NonUnitalNonAssocSemiring R](h:graded w A)(k:graded w B): graded w (A*B):= by
 intro i j hij
 rw [Matrix.mul_apply]
 apply Finset.sum_eq_zero; intro b _; by_cases hb:w i=w b
 · rw [k (fun ht=>hij (hb.trans ht)),mul_zero]
 rw [h hb,zero_mul]

theorem right_block [Fintype J][NonUnitalNonAssocSemiring R](k:graded w B)(A:Square J R): isolate w (A*B)=isolate w A * B:= by
  ext i j
  simp only [isolate,Matrix.of_apply,Matrix.mul_apply]
  split <;> rename_i h
  · apply Finset.sum_congr rfl; intro b _; split
    · rfl
    rename_i ht
    rw [k (fun hh=>ht (h.trans hh.symm)),mul_zero,mul_zero]
  symm; apply Finset.sum_eq_zero; intro b _; split
  · rename_i he; rw [k (fun hu=> h (he.trans hu)),mul_zero]
  rw [zero_mul]

theorem left_block [Fintype J][NonUnitalNonAssocSemiring R](h:graded w A)(B:Square J R): isolate w (A*B)=A*isolate w B:= by
  ext i j
  simp only [isolate,Matrix.of_apply,Matrix.mul_apply]
  split <;> rename_i he
  · apply Finset.sum_congr rfl; intro b _; split
    · rfl
    rename_i ht
    rw [h (fun hh=>ht (hh.symm.trans he)),zero_mul,zero_mul]
  symm; apply Finset.sum_eq_zero; intro b _; split
  · rename_i hk; rw [h (fun hu=>he (hu.trans hk)),zero_mul]
  rw [mul_zero]

theorem isolates_one [DecidableEq J][One R][Zero R]: isolate w (1:Square J R)=1:= invariant graded.one

@[simp] theorem piece_isolate [Semiring R](A:Square J R⟦X⟧)(k:ℕ): piece k (isolate w A)=isolate w (piece k A):=Matrix.ext fun i j=>by
  by_cases he:w i=w j <;> simp only [piece_apply,isolate,Matrix.of_apply,he,↓reduceIte,map_zero]

theorem piece_all [Semiring R]{A:Square J R⟦X⟧}:graded w A ↔ ∀ k,graded w (piece k A):=by
  constructor
  · intro h k i j he; simp [h he]
  intro h i j hj; ext k; simpa only [map_zero,piece_apply] using @h k i j hj

private theorem same {R:Type*}[CommRing R][Fintype J]{A:Square J R}:
   graded w A ↔ A∈ (Constraints.sameGrade w).vary:=by
  change graded w A ↔ Matrix.BlockTriangular A _ ∧ Matrix.BlockTriangular A w
  constructor
  · intro h; exact ⟨fun _ _ he=>h (ne_of_lt he),fun _ _ he=>h (ne_of_gt he)⟩
  rintro ⟨h,e⟩ i j he; obtain ht|ht:=lt_or_gt_of_ne he
  · exact h ht
  exact e ht

theorem asLaw {R:Type*}[CommRing R][Fintype J][DecidableEq J]{A:Square J R⟦X⟧}(hz: nearId A):
    graded w A ↔ (Constraints.sameGrade w).Lawful A:=by
  rw [piece_all]; constructor
  · intro h; exact ⟨hz,fun _=>same.mp (h _)⟩
  intro h k; cases k with
  |zero=>rw [hz]; exact graded.one
  |succ=> exact same.mpr (h.positive (by omega))

theorem Law_inv {R:Type*}[CommRing R][Fintype J][DecidableEq J]{A:Square J R⟦X⟧}(h:graded w A)(hz:nearId A):
   graded w (squareInv A):=(asLaw (squareInv_base _)).mpr (((asLaw hz).mp h).squareInv)

theorem Law_subs {R:Type*}[CommRing R][Fintype J][DecidableEq J]{A:Square J R⟦X⟧}{p:PowerSeries R}(h:graded w A)(hz:nearId A)(ha:Anchored p):
   graded w (subs p A):= (asLaw (hz.subs ha)).mpr (((asLaw hz).mp h).subs ha)
end graded

/-- unit index need not have weight zero for this lemma. -/
structure Permits (J: Type*) (w:J→ℕ)[Fintype J] (L:Constraints ℝ J):Prop where
   split {A}: A∈ L.vary → isolate w A∈L.vary
   lowers {A}:A∈L.vary → ∀ i j,w i<w j→ A i j=0
namespace Permits
variable [Fintype J]
variable {w}

theorem position {I:Type*}{H:I→Square J ℝ}(hh:∀ i, graded w (H i))(b:J):
    Permits J w (Constraints.position b w H):=by
  constructor
  · intro a ha
    obtain ⟨_,hp,hv⟩ := Constraints.mem_position_iff.mp ha
    apply Constraints.mem_position_iff.mpr
    exact ⟨fun _ _ hi=> graded.isIsolated a (ne_of_lt hi),fun i=>by simp only [isolate,Matrix.of_apply,hp,ite_self],fun i=>by rw [←graded.right_block (hh i),←graded.left_block (hh i),hv i]⟩
  intro a ha; exact (Constraints.mem_position_iff.mp ha).1

theorem tests {u v:Constraints ℝ J}(h:Permits J w u)(h₂:u.vary=v.vary):Permits J w v:=by
  constructor
  · rw [←h₂]; exact fun a=>h.split a
  rw [←h₂]; exact fun a=>h.lowers a
end Permits
end YM.RG11.Scale
