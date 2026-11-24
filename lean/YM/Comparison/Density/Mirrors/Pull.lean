import YM.Comparison.Density.Mirrors.Axis

/-!
# Mirroring actual group fields (not independent multilinear slots)

All edge reversals use the inverse at the shifted stored edge. All lifts
are in lattice units. In particular the pulled field contains complete path
information and obeys the **nonlinear** compatibility identities. The cube identity follows on these fields from their three
one-edge connectors, without a null-tensor iteration in a freely generated
curvature alphabet.
We will test on these genuine realizable arguments all the way through.
-/

set_option autoImplicit false
namespace YM.Comparison.Density.Mirrors
open Function Lattice

variable {n : Side}

def reflectAt (k : Side) (x : Site (quad k)) : Cover := wave k ∘ x

lemma reflectAt_mem (k : Side) (x : Site (quad k)) : reflectAt k x ∈ box k.val :=
  box_test.mpr ⟨fun i => (wave_range k (x i)).1,fun i => (wave_range k (x i)).2⟩

lemma reflectAt_signed (k : Side) (x : Site (quad k)) (s : Signed) :
    reflectAt k (s.act x)=s.act (reflectAt k x) := by
  funext i
  obtain ⟨j,rfl⟩ := s.perm.surjective i
  change wave k (s.act x (s.perm j))=_
  rw [Signed.act_at,Signed.act_at]
  split
  · rw [wave_neg]; rfl
  rfl

def risen (k : Side) (x : Site (quad k)) (i : Axis) : Step :=
  if wave k (x i+1)=wave k (x i)+1 then posDir i else negDir i

/-- Direction in the old field of a step in the reflected field. -/
def mirrored (k : Side) (x : Site (quad k)) (d : Step) : Step :=
  if d.neg then (risen k (x-step d.dir) d.dir).rev else risen k x d.dir

@[simp] lemma mirrored_pos (k : Side) (x : Site (quad k)) (i : Axis) : mirrored k x (posDir i) = risen k x i := rfl
@[simp] lemma mirrored_neg (k : Side) (x : Site (quad k)) (i : Axis) : mirrored k x (negDir i) = (risen k (x-step i) i).rev := rfl

lemma reflect_pos (k : Side) (x : Site (quad k)) (i : Axis) :
    reflectAt k (x+step i)=reflectAt k x+(risen k x i).vec := by
  unfold risen
  split
  · rename_i hh
    funext j
    by_cases hj : i=j
    · subst j
      simpa [reflectAt] using hh
    simp [reflectAt,Ne.symm hj]
  rename_i hh
  have hz:= (wave_step k (x i)).resolve_left hh
  funext j
  by_cases hj : i=j
  · subst j
    simpa [reflectAt,sub_eq_add_neg] using hz
  simp [reflectAt,Ne.symm hj]

lemma reflect_walkStep (k : Side) (x : Site (quad k)) (d : Step) :
    reflectAt k (x+d.vec)=reflectAt k x+(mirrored k x d).vec := by
  rcases d with ⟨i,h|h⟩
  · exact reflect_pos ..
  change reflectAt k (x+(negDir i).vec)=reflectAt k x+(mirrored k x (negDir i)).vec
  rw [Step.vec_neg,← sub_eq_add_neg,mirrored_neg,Step.vec_rev]
  have ht:= reflect_pos k (x-step i) i
  rw [sub_add_cancel] at ht
  rw [ht]; simp

lemma reflect_wrap (k : Side) {z : Cover} (h : z∈box k.val) : reflectAt k (wrap (quad k) z)=z := by
  funext i; exact wave_core _ _ (box_test.mp h|>.1 i) (box_test.mp h|>.2 i)

private lemma step_unique (p q : Step) (h : (p.vec : Cover) = q.vec) : p=q := by
  obtain ⟨i,t|t⟩:=p <;> obtain ⟨j,u|u⟩:=q
  · change step i = (step j : Cover) at h
    by_contra! he
    have hg : i ≠ j := fun hu => he (by rw [hu])
    simpa [hg] using congr_fun h i
  · have e:=congr_fun h i
    by_cases hz:i=j <;> simp [Step.vec,hz] at e
  · have e:=congr_fun h i
    by_cases hz:i=j <;> simp [Step.vec,hz] at e
  change -(step i : Cover) = -(step j : Cover) at h
  by_contra! he
  have hg : i ≠ j := fun hu => he (by rw [hu])
  simpa [hg] using congr_fun h i

lemma mirrored_rotate (k : Side) (x : Site (quad k)) (d : Step) (s : Signed) :
    mirrored k (s.act x) (d.rotate s)=(mirrored k x d).rotate s := by
  apply step_unique
  apply add_left_cancel (a:=s.act (reflectAt k x))
  conv_lhs => lhs; rw [← reflectAt_signed]
  rw [← reflect_walkStep,Step.vec_rotate, ← Signed.act_add, reflectAt_signed,
    reflect_walkStep, Step.vec_rotate, ← Signed.act_add, Signed.act_add]

/-- If a signed-affine symmetry of the test torus preserves the mirror map,
then it carries every step to one reading the same old link in the same
direction, including at endpoints. -/
lemma mirrored_fixed (k : Side) (s : Signed) (b : Site (quad k))
    (h : ∀ x, reflectAt k (affine s b x)=reflectAt k x) (x : Site (quad k)) (d : Step) :
    mirrored k (affine s b x) (d.rotate s) = mirrored k x d := by
  apply step_unique
  apply add_left_cancel (a:=reflectAt k x)
  conv_lhs => lhs; rw [← h]
  rw [← reflect_walkStep,← reflect_walkStep, Step.vec_rotate,
    show affine s b x+s.act d.vec=affine s b (x+d.vec) by
      unfold affine; rw [Signed.act_add]; abel,h]

variable {K : Type*} [Group K]

def field (k : Side) (A : Links ℤ K) : Links (Per (quad k)) K := fun e=>
  (risen k e.1 e.2).read A (reflectAt k e.1)

lemma field_read (k : Side) (A : Links ℤ K) (x : Site (quad k)) (d : Step) :
    d.read (field k A) x=(mirrored k x d).read A (reflectAt k x) := by
  rcases d with ⟨i,q|q⟩
  · rfl
  change (negDir i).read (field k A) x =(mirrored k x (negDir i)).read A (reflectAt k x)
  rw [Step.neg_read,mirrored_neg]
  have he:= reflect_pos k (x-step i) i
  rw [sub_add_cancel] at he
  rw [he, Step.read_rev]; rfl

lemma field_gauge (t : Cover→ K) (k : Side) (A : Links ℤ K) :
    field k (gauge t A) = gauge (fun x => t (reflectAt k x)) (field k A) := by
  funext e
  obtain ⟨x,i⟩:= e
  unfold field gauge
  -- use gauge_read
  change (risen k x i).read (gauge t A) _ = _
  rw [Step.gauge_read, ← reflect_pos]

/-- Orthogonal signed change of box, mirror the WHOLE field.
Sites where two descriptions of the mirror meet obey it literally. -/
lemma field_signed (k : Side) (s : Signed) (A : Links ℤ K) :
    field k (pull s 0 A)=pull s 0 (field k A) := by
  funext e
  obtain ⟨x,i⟩:=e
  conv_rhs => rw [pull]
  change (risen k x i).read _ _=((posDir i).rotate s).read _ (affine s 0 x)
  rw [Step.pull_read, field_read,affine,affine, add_zero,add_zero,mirrored_rotate,reflectAt_signed,mirrored_pos]

lemma field_fixed (k : Side) (s : Signed) (b : Site (quad k))
    (h : ∀ x, reflectAt k (affine s b x)=reflectAt k x) (A : Links ℤ K) :
    pull s b (field k A)=field k A := by
  funext e
  obtain ⟨x,i⟩ := e
  change ((posDir i).rotate s).read _ (affine s b x)= _
  rw [field_read, mirrored_fixed _ _ _ h, h]; rfl

def mirrorPath (k : Side) (x : Site (quad k)) : Walk → Walk
  | []=>[]
  | d::ds=> mirrored k x d :: mirrorPath k (x+d.vec) ds

lemma same_length (k : Side) (x : Site (quad k)) (w : Walk) :
    (mirrorPath k x w).length=w.length := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=>rw [mirrorPath,List.length_cons,ih,List.length_cons]

/-- Every path, not just a small-link approximation; even if the pointer
crosses a seam in the fictitious test torus. -/
lemma field_path (k : Side) (A : Links ℤ K) (x : Site (quad k)) (w : Walk) :
    travel (field k A) x w = travel A (reflectAt k x) (mirrorPath k x w) := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=> rw [mirrorPath,travel,field_read,ih,travel,reflect_walkStep]

lemma mirror_visits (k : Side) (x : Site (quad k)) (w : Walk) :
    visits (reflectAt k x) (mirrorPath k x w)= (visits x w).map (reflectAt k) := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=> rw [mirrorPath,visits,← reflect_walkStep,ih]; rfl

lemma mirror_end (k : Side) (x : Site (quad k)) (w : Walk) :
    stop (reflectAt k x) (mirrorPath k x w)=reflectAt k (stop x w) := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=> rw [mirrorPath,stop,← reflect_walkStep,ih]; rfl

/-- Mirror compatibility is kept on real fields. In particular the two
actual compositions of the elementary swaps agree. Here with the three
one-edge connectors on the shifted curvature data before
reading Lie coordinates. -/
theorem cube {L : Type*} [AddCommGroup L] [One L]
    (U : Links L K) (x : Four L) (a b c : Axis) :
    travel U x (square a b) *
      (U (x,b) * travel U (x+step b) (square a c) * (U (x,b))⁻¹) *
      travel U x (square b c) =
    (U (x,a) * travel U (x+step a) (square b c) * (U (x,a))⁻¹) *
      travel U x (square a c) *
      (U (x,c) * travel U (x+step c) (square a b) * (U (x,c))⁻¹) := by
  have ht (w : Four L) (i j : Axis) : travel U w (square i j) =
      U (w,i)*U (w+step i,j)*(U (w+step j,i))⁻¹*(U (w,j))⁻¹ := by
    have he (w : Four L) (i j : Axis) : w+step i+step j-step i = w+step j := by abel
    simp [square,travel,← sub_eq_add_neg,he,mul_assoc]
  simp only [ht]
  rw [add_right_comm x (step b) (step a),add_right_comm x (step b) (step c),
      add_right_comm x (step a) (step c)]
  group
end YM.Comparison.Density.Mirrors
