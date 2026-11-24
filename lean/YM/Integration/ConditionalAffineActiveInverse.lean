import YM.Integration.ConditionalCovarianceCutoff
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore

/-! The actual no-hole row mask, embedded finite resolvent, and the
corresponding original signed no-hole affine load in the fine coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalNoHoleRows
open Function Finset Lattice Wilson RG Precision Exterior Tree Pressure Next.SectorChange Next.SectorChange.Rows
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {g : Ratio c f} {S : StepData c f}

private theorem source_parent (F : Forest g) (z : Site f) (hz : leaf g z) :
    g.parent ((F.up z).used z).1 = g.parent z := by
  let d := F.up z
  have h := F.stays z hz
  change g.parent (z+d.vec)=g.parent z at h
  change g.parent (d.used z).1=g.parent z
  cases hd : d with
  | mk k b =>
    rw [hd] at h
    cases b <;> simp only [Step.used,Bool.false_eq_true,↓reduceIte,Step.vec,←sub_eq_add_neg] at h ⊢
    exact h

/-- This works for each specified axis, even in a one-block periodic torus. -/
theorem free_over (F : Forest g) (y : Site c) (a : Axis) :
    ∃ x : Site f, g.parent x=y ∧ (x,a)∉F.trunks := by
  classical
  let U : Finset (Site f) := Finset.univ.filter fun x => g.parent x=y
  let root := g.embed y
  let links (x : Site f) : Edge (Site f) := (x,a)
  let parentEdge (z : Site f) : Edge (Site f) := (F.up z).used z
  have hroot : root∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,g.embed_parent _⟩
  by_contra h
  have hit : ∀ x∈U, links x∈F.trunks := by
    intro x hx
    exact not_not.mp fun he => h ⟨x,(Finset.mem_filter.mp hx).2,he⟩
  have subset : U.image links ⊆ (U.erase root).image parentEdge := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z,hz,hze⟩ := (F.trunk_mem_iff _).mp (hit x hx)
    have hp := source_parent F z hz
    rw [hze] at hp
    have hv : g.parent z=y := hp.symm.trans (Finset.mem_filter.mp hx).2
    have hn : z≠root := by
      change z≠g.embed y
      rw [←hv]
      exact hz
    exact Finset.mem_image.mpr ⟨z,Finset.mem_erase.mpr ⟨hn,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩,hze⟩
  have hl : (U.image links).card=U.card := U.card_image_of_injective fun i j h => congrArg Prod.fst h
  have hL := (Finset.card_le_card subset).trans (Finset.card_image_le (s:=U.erase root) (f:=parentEdge))
  rw [hl] at hL
  exact (Finset.card_erase_lt_of_mem hroot).not_ge hL

local notation "emptyStore" => (⟨∅,∅,∅⟩ : Stores S)

/-- The signed stencil contains the surviving genuine active link in its
center block. The proof uses the actual `shots` and actual `Native.every`. -/
theorem supported (F : Forest S.ratio) (x : ℝ) (s : Signed) (i : Where S) :
    curb (shots S x) emptyStore F x s i := by
  obtain ⟨z,hz,ht⟩ := free_over F (s.act (roots S i)) (0:Axis)
  refine ⟨Native.every F x ⟨(z,0),ht⟩,?_⟩
  apply (contains s i _).mpr
  change separation (s.act (roots S i)) (S.ratio.parent z) ≤ span S.patch x
  simp [hz]

theorem kept (F : Forest S.ratio) (x : ℝ) (i : Slots S) :
    Rows.keep x (shots S x) emptyStore F i := by
  rcases i with ⟨s,p|b⟩
  · exact supported F x s (.inl p.1)
  exact supported F x s (.inr b)

/-- Both the signed affine source and every curved column are unmasked on
the original no-hole chart, even when the value has no field derivative. -/
theorem all (F : Forest S.ratio) (x : ℝ) (z : LogArray G (Slots S)) :
    Rows.restrict x (shots S x) emptyStore F z = slip • z := by
  funext i
  exact if_pos (kept F x i)

theorem sourceGuard_zero (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (V : Config G c) (k : S.Choices) :
    Rows.restrict x (shots S x) emptyStore F (Rows.base T x V k) - slip • Rows.base T x V k = 0 := by
  rw [all,sub_self]

end YM.Integration.ConditionalNoHoleRows

namespace YM.Integration.ConditionalAffineActiveInverse
open Function Lattice RG Wilson Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt
open scoped Classical Matrix.Norms.Frobenius BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def deposit (e : β ↪ α) (A : Matrix β β ℝ) := insertion e * A * (insertion e).transpose

private lemma product (e : β ↪ α) (A B : Matrix β β ℝ) :
    deposit e A * deposit e B = deposit e (A*B) := by
  unfold deposit
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (insertion e).transpose (insertion e),Shell.pin,Matrix.one_mul]

private lemma right_zero (e : β ↪ α) (A : Matrix β β ℝ) : deposit e A * Shell.off e = 0 := by
  rw [deposit,Matrix.mul_assoc,Shell.barred_left,Matrix.mul_zero]

private lemma left_zero (e : β ↪ α) (A : Matrix β β ℝ) : Shell.off e * deposit e A = 0 := by
  rw [deposit,←Matrix.mul_assoc,←Matrix.mul_assoc,Shell.barred,Matrix.zero_mul,Matrix.zero_mul]

/-- Block inverse for the exact principal erosion, including the erased
diagonal, valid with no cardinal or choice agreement between forests. -/
theorem inverse (e : β ↪ α) (A : Matrix α α ℝ) (h : IsUnit (A.submatrix e e).det) :
    (Shell.pad e A)⁻¹ = deposit e (A.submatrix e e)⁻¹ + Shell.off e := by
  apply Matrix.inv_eq_right_inv
  rw [Shell.pad,Shell.sliced]
  change (deposit e (A.submatrix e e) + Shell.off e) * (deposit e (A.submatrix e e)⁻¹ + Shell.off e) = 1
  rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,product,right_zero,left_zero,Shell.off_off,
    Matrix.mul_nonsing_inv _ h,add_zero,zero_add]
  unfold deposit Shell.off Shell.rim
  rw [Matrix.mul_one]
  abel

omit [Fintype α] [DecidableEq β] in
private lemma total (e : β ↪ α) : Shell.rim e + Shell.off e = 1 := by
  unfold Shell.off
  abel

omit [Fintype α] in
private lemma deposit_one (e : β ↪ α) : deposit e 1=Shell.rim e := by
  rw [deposit,Matrix.mul_one,Shell.rim]

private lemma split_shift (e : β ↪ α) (A : Matrix α α ℝ) (u : ℝ) :
    Shell.pad e A + u • (1 : Matrix α α ℝ) =
      deposit e (A.submatrix e e + u • (1 : Matrix β β ℝ)) + (1+u) • Shell.off e := by
  have he : u • (1 : Matrix α α ℝ) = u • Shell.rim e + u • Shell.off e := by
    rw [←smul_add,total]
  have fd : deposit e (A.submatrix e e+u • (1 : Matrix β β ℝ)) =
      deposit e (A.submatrix e e) + u • Shell.rim e := by
    unfold deposit Shell.rim
    rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  rw [fd,Shell.pad,Shell.sliced,he,add_smul,one_smul]
  unfold deposit
  abel

private lemma diagonal_product (e : β ↪ α) (A B : Matrix β β ℝ) (r s : ℝ) :
    (deposit e A + r • Shell.off e) * (deposit e B + s • Shell.off e) =
      deposit e (A*B)+(r*s) • Shell.off e := by
  rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,product,Matrix.mul_smul,right_zero,smul_zero,
    Matrix.smul_mul,left_zero,smul_zero,Matrix.smul_mul,Matrix.mul_smul,Shell.off_off,smul_smul,
    add_zero,zero_add]

/-- Positive spectral parameter on the erased diagonal. The original
active principal resolvent is the other block for exactly the same u. -/
theorem shifted (e : β ↪ α) (A : Matrix α α ℝ) (u : ℝ) (hu : 0≤u)
    (h : IsUnit (A.submatrix e e+u • 1).det) :
    resolve (Shell.pad e A) u = deposit e (resolve (A.submatrix e e) u) +
      (1+u)⁻¹ • Shell.off e := by
  unfold resolve
  rw [split_shift]
  apply Matrix.inv_eq_right_inv
  rw [diagonal_product,Matrix.mul_nonsing_inv _ h,deposit_one,
    mul_inv_cancel₀ (by linarith : 1+u≠0),one_smul,total]

/-- On the retained physical coordinate array the inactive offset is zero. -/
theorem «on» (e : β ↪ α) (A : Matrix α α ℝ) (u : ℝ) (hu : 0≤u)
    (h : IsUnit (A.submatrix e e+u • 1).det) (i j : β) :
    resolve (Shell.pad e A) u (e i) (e j) = resolve (A.submatrix e e) u i j := by
  let B := resolve (A.submatrix e e) u
  have hd : (deposit e B).submatrix e e = B := by
    rw [←insertion.compress,deposit]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc (insertion e).transpose (insertion e),Shell.pin,Matrix.one_mul,Matrix.mul_one]
  rw [shifted e A u hu h,Matrix.add_apply,Matrix.smul_apply,Shell.off_test]
  simp only [Set.mem_range_self,not_true_eq_false,and_false,if_false,smul_zero,add_zero]
  exact congr_fun₂ hd i j

/-- Entries on the erased diagonal have no curvature dependence. This is
the equality required inside the paired half-log spectral integral. -/
theorem off_diagonal (e : β ↪ α) (A : Matrix α α ℝ) (u : ℝ) (hu : 0≤u)
    (h : IsUnit (A.submatrix e e+u • 1).det) (i : α) (hi : i∉Set.range e) :
    resolve (Shell.pad e A) u i i = (1+u)⁻¹ := by
  have hb (j : β) : e j≠i := fun h => hi ⟨j,h⟩
  have hf (B : Matrix β β ℝ) : deposit e B i i=0 := by
    simp [deposit,Matrix.mul_apply,insertion,hb]
  rw [shifted e A u hu h,Matrix.add_apply,Matrix.smul_apply,Shell.off_test,hf]
  simp [hi]

/-- The projection identity also holds for each admitted actual cutoff. -/
theorem admitted {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (t : S.Choices)
    (p : Clip) (W : PathData G) (r : Admit) (B : Vec G c 1) (h : IsUnit (primary S F t p W r B).det) :
    deposit (freeTo G S F) (primary S F t p W r B)⁻¹ =
      action (whole S F t p W r) 0 B - Shell.off (freeTo G S F) := by
  change _ = (Shell.pad (freeTo G S F) (block S t p W r B) + 0 • 1)⁻¹ - _
  have hQ : IsUnit ((block S t p W r B).submatrix (freeTo G S F) (freeTo G S F)).det := h
  rw [zero_smul,add_zero,inverse (freeTo G S F) (block S t p W r B) hQ,add_sub_cancel_right]
  rfl

/-- In the genuine curved FIaf coordinates, the physical full covariance
is the complete resolvent minus its original inactive-coordinate identity. -/
theorem original {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (t : S.Choices)
    (p : Clip) (W : PathData G) (B : Vec G c 1) (h : IsUnit (primary S F t p W all B).det) :
    deposit (freeTo G S F) (primary S F t p W all B)⁻¹ =
      action (whole S F t p W all) 0 B - Shell.off (freeTo G S F) := by
  exact admitted S F t p W all B h

/-- At fixed physical `v` the inactive projector changes only on the
changed diagonal there, even when the cardinalities of the active keys
differ. It is exactly independent of the coarse background. -/
theorem projector_away {G : Gauge} {c f : Side} (S : StepData c f) (r s : Reserve S)
    (v : Site c) (h : ∀ o, o ≠ v → r o = s o) (i j : raw G f)
    (hi : i≠j ∨ home S i≠v) :
    Shell.off (freeTo G S (allot r)) i j = Shell.off (freeTo G S (allot s)) i j := by
  have hmask := suits G v (ConditionalTreeCovarianceJets.change_draw r s v h)
  simp only [Shell.off,Matrix.sub_apply,Shell.indicator]
  rcases hi with hij|hr
  · simp [hij]
  simp only [hmask i hr]

end YM.Integration.ConditionalAffineActiveInverse

namespace YM.Integration.ConditionalAffineActiveInverse
open Function Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube Pressure.Stores
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian FreeResolvent FreeResolvent.Affine FreeResolvent.TestD Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- The literal finite signed load uses the actual retained physical rows.
On the no-hole stage the selected free inverse acts on these same rows
when one replaces the retained coordinate matrix by its ambient version. -/
theorem physical_load (T : Tube G S) (F : Forest S.ratio) (k : S.Choices) (x : ℝ) (B : Vec G c 1)
    (h : IsUnit (primary S F k T.high T.up (shorter (till x)) B).det) :
    let V := represent (decode B)
    let b := Rows.base T x V k
    let D : Matrix (Rows.Receipt G S) (raw G f) ℝ := Matrix.of fun i j =>
      tape.symm (slip • Rows.bump T x V k (collect G (decode (ray G f j)))) i
    let e := freeTo G S F
    let Q := primary S F k T.high T.up (shorter (till x)) B
    deposit e Q⁻¹ *ᵥ (D.transpose *ᵥ tape.symm (Rows.restrict x (shots S x) (⟨∅,∅,∅⟩:Stores S) F b)) =
      (action (whole S F k T.high T.up (shorter (till x))) 0 B - Shell.off e) *ᵥ (D.transpose *ᵥ tape.symm (slip • b)) := by
  intro V b D e Q
  rw [ConditionalNoHoleRows.all F x b]
  exact congrArg (fun A => A *ᵥ (D.transpose *ᵥ tape.symm (slip • b)))
    (admitted S F k T.high T.up (shorter (till x)) B h)

end YM.Integration.ConditionalAffineActiveInverse
