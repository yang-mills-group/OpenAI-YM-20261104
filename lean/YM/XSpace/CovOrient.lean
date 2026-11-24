import YM.XSpace.WickLocal
/-! # Signed space actions before subtraction -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Laurent Bloch Exterior Matrix
open Next.Free Precision Further.CorrectedLift Further.FreeCovariance.KP Next.Rank Normal Spindle
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff
section path
variable {R : Type*} [AddCommGroup R] [One R]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (A : Edge (Four R) → V)

-- additive orientation at canonical base

def lining (x : Four R) (w : Walk) := Multiplicative.toAdd (travel (Multiplicative.ofAdd ∘ A) x w)
def pulling (s : Signed) (o : Four R) (i : Edge (Four R)) := Multiplicative.toAdd (pull s o (Multiplicative.ofAdd ∘ A) i)

omit [Module ℝ V] in
lemma lining_link (x : Four R) (w : Walk) : lining A x w= linkSum A x w := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w h=>
    rw [lining, travel, linkSum]; rw [← h]; rcases a with ⟨a,b|b⟩ <;> rfl

omit [Module ℝ V] in
lemma lining_n (a b : Step) (x : Four R) : lining A (x+a.vec) (oriented a.rev b)= - lining A x (oriented a b) := by
  rw [lining,lining,oriented_swap b a.rev,oriented_next]; simp [mul_comm ((Step.read .. )⁻¹ : Multiplicative V),mul_assoc] -- inspect

omit [Module ℝ V] in
lemma lining_swap (x : Four R) (a b : Step) : lining A x (oriented a b)= -lining A x (oriented b a) := by simp_rw [lining, oriented_swap b a]; rfl

def ng (a : Step) := if a.neg then (-1:ℝ) else 1

lemma lining_pos (x : Four R) (a b : Step) : lining A x (oriented a b)=(ng a*ng b) • lining A (atFace x a b) (square a.dir b.dir) := by
  have he (x : Four R) (i : Axis) (b : Step) : lining A x (oriented (posDir i) b) = ng b • lining A (atFace x (posDir i) b) (square i b.dir) := by
    rcases b with ⟨j,g|g⟩
    · simp [atFace,posDir,ng]; rfl
    change lining A x (oriented (posDir i) (negDir j)) = _
    rw [lining_swap, ← lining_n A]; simp only [atFace,posDir,negDir,Bool.false_eq_true,↓reduceIte,ng,add_zero,neg_smul,one_smul]; change lining A _ (oriented (posDir j) (posDir i))= _; rw [lining_swap A (x+_) (posDir j) (posDir i)]; rfl
  rcases a with ⟨i,p|p⟩
  · simpa only [ng,posDir,Bool.false_eq_true,↓reduceIte,one_mul] using he x i b
  change lining A x (oriented (negDir i) b) =_
  rw [← neg_neg (lining A x _),← lining_n,Step.rev_neg,he]; simp only [atFace,ng,posDir,negDir,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul,add_zero,neg_smul]

-- orientation from the image square
def faceS (s : Signed) (p : PlaqAxes) : ℝ :=
  ng ((posDir p.val.1).rotate s)*ng ((posDir p.val.2).rotate s)*(if s.perm p.val.1<s.perm p.val.2 then (1:ℝ) else -1)
lemma faceS_one (s : Signed) (p : PlaqAxes) : faceS s p*faceS s p=1 := by unfold faceS ng; split_ifs <;> ring

lemma send_lin (x : Four R) (s:Signed) (p : Face R) :
    lining (pulling A s x) p.1 (square p.2.val.1 p.2.val.2)=faceS s p.2 • lining A (Face.send s x p).1 (square (Face.send s x p).2.val.1 (Face.send s x p).2.val.2) := by
  let a:= p.2.val.1; let b:= p.2.val.2
  unfold lining
  rw [show Multiplicative.ofAdd ∘ pulling A s x=pull s x (Multiplicative.ofAdd ∘ A) from rfl, travel_pull,show List.map _ (square _ _)=oriented ((posDir a).rotate s) ((posDir b).rotate s) by
    rw [show square _ _=oriented (posDir a) (posDir b) from rfl]; simp only [oriented,List.map_cons,List.map_nil, Step.rev_rotate]]
  change lining A _ (oriented _ _)=_
  rw [lining_pos]
  change (ng ((posDir a).rotate s) * ng ((posDir b).rotate s)) • lining A _ (square _ _) = (faceS s p.2) • lining A _ (square (min (s.perm a) (s.perm b)) (max (s.perm a) (s.perm b)))

  rcases lt_or_gt_of_ne (s.perm.injective.ne (show a ≠ b from p.2.property.ne)) with h|h
  · unfold faceS; rw [min_eq_left h.le,max_eq_right h.le,if_pos h, mul_one]; rfl
  unfold faceS; rw [min_eq_right h.le,max_eq_left h.le,if_neg (not_lt.mpr h.le),mul_neg,mul_one,neg_smul]
  change _ • lining A _ (oriented (posDir (s.perm a)) (posDir (s.perm b))) =_; rw [lining_swap A _ (posDir (s.perm a)),smul_neg]; rfl
end path

variable (G : Gauge)
def spin (s : Signed) (i : AKey G): AKey G :=
  let p := Face.send (R:=ℤ) s 0 (i.1,i.2.1)
  (p.1,p.2,i.2.2)
lemma spin_curl (A : CoverC G) (s : Signed) (i : AKey G) : curlC G (pulling A s 0) i= faceS s i.2.1*curlC G A (spin G s i) := by
  have he := send_lin A (0:Cover) s (i.1,i.2.1); simp only [lining_link] at he
  exact congr_arg (fun x:G.Color=> x i.2.2) he

variable {n : Side}

def spins (s : Signed) : FKey G n→ FKey G n:=fun i=> (Face.send s (0:Site n) i.1,i.2)
def spinM (s:Signed) := of (fun i j:FKey G n=> if j=spins G s i then faceS s i.1.2 else 0)
lemma spools (s:Signed) (f : FKey G n → ℝ) (i:FKey G n) : (spinM G s *ᵥ f) i= faceS s i.1.2*f (spins G s i):= by simp [spinM,mulVec,dotProduct,ite_mul]
lemma spins_closes (s:Signed) (i:AKey G): spins G s (closes G n i)=closes G n (spin G s i) := by
  simp only [spin, spins, closes, Face.send, Face.lower, affine, atFace, wrap_signed, add_zero, map_add]; simp only [apply_ite (wrap n),wrap_vec,map_zero]

lemma spins_field (A : Pot G n) (s:Signed): spinM G s *ᵥ fields G n A=fields G n (pulling A s 0) := by
  funext i
  let j : AKey G:= (lift i.1.1,i.1.2,i.2)
  have hx e : inCover G n (pulling A s 0) e= pulling (inCover G n A) s 0 e := by
    unfold inCover pulling; apply congr_arg
    simp [pull,Step.rotate,Step.read,Step.used, posDir,affine]; split <;> simp_all
  rw [spools,← show closes G n j=i from by simp [closes,j], spins_closes, ← curl_inCover, ← curl_inCover, _root_.funext hx]
  exact (spin_curl G (inCover G n A) s j).symm

lemma spins_inj (s : Signed) : Injective (spins G (n:=n) s) := fun x y h=> Prod.ext (Face.injective_send _ _ (congr_arg Prod.fst h)) (show (spins G s x).2=(spins G s y).2 from congr_arg Prod.snd h)

lemma spin_ortho (s : Signed) : spinM G (n:=n) s * (spinM G s).transpose=1:= by
  ext i j; rw [Matrix.one_apply]
  by_cases h : i=j
  · subst j; simp [Matrix.mul_apply,spinM,ite_mul,faceS_one ..]
  simp [h,Matrix.mul_apply,spinM,ite_mul, (spins_inj G s).ne (Ne.symm h)]

lemma spin_kernel (s : Signed) : (spinM G s)*kernel G n*(spinM G s).transpose=kernel G n := by
  let R:= kernel G n; let L:= spinM G (n:=n) s
  have he : R*(L*R)= L*R := by
    apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec]; rw [← Matrix.mulVec_mulVec]
    obtain ⟨A,hA⟩:= project_into G n x; change R *ᵥ x=_ at hA; rw [hA,spins_field]; exact project_fixes ..
  -- other direction using inverse-space periodic identity on potentials
  have hL : L.transpose * L=1:= mul_eq_one_comm.mpr (spin_ortho G s)
  have hp : R*(L.transpose*R)= L.transpose*R := by
    apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec]; rw [← Matrix.mulVec_mulVec]
    obtain ⟨A,hA⟩:= project_into G n x; change R *ᵥ x=_ at hA
    let B:= pulling A s⁻¹ 0
    have hx: pulling B s 0=A := by
      funext i; change Multiplicative.toAdd (pull s (0:Site n) (pull s⁻¹ 0 (Multiplicative.ofAdd ∘ A)) i)=_; rw [pull_pull]
      rw [inv_mul_cancel]; simp [affine]
    rw [hA,← show L *ᵥ fields G n B= fields G n A by rw [spins_field,hx], Matrix.mulVec_mulVec _ L.transpose L,hL,Matrix.one_mulVec]; exact project_fixes ..
  have H:= congr_arg Matrix.transpose hp; rw [Matrix.transpose_mul, Matrix.transpose_mul,show R.transpose=R from kernel_symm ..,Matrix.transpose_transpose,Matrix.mul_assoc, he] at H
  change L*R*L.transpose=R; rw [H, Matrix.mul_assoc, spin_ortho, Matrix.mul_one]

-- Address pull coloring

def signedM (s:Signed) (i:AKey G) := Finsupp.single (spin G s i) (↑(faceS s i.2.1):ℂ)
lemma reads_spin (s:Signed) (A : CoverC G): Normal.reads (signedM G s) (fun i=>(curlC G A i:ℂ))= fun i=>(curlC G (pulling A s 0) i:ℂ) := by funext i; simp [Normal.reads,signedM,spin_curl]
lemma spins_cov (s:Signed) : scope (signedM G s) (WickK G)= WickK G := by
  apply Normal.Symmetric.ext; funext i j
  have he (n : Side) := congr_fun (congr_fun (spin_kernel G (n:=n) s) (closes G n i)) (closes G n j)
  let r (x:AKey G) := (↑(faceS s x.2.1):ℂ)
  have hp n:r i * r j * (self G n).cov (spin G s i) (spin G s j)= (self G n).cov i j:=by
    simp only [self,match_name,beats,complexK,r]
    have HH := he n; simp only [Matrix.mul_apply,spinM,Matrix.transpose_apply, of_apply,ite_mul,mul_ite,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_zero] at HH
    simp at HH
    rw [← HH]; rw [spins_closes,spins_closes]; simp only [Complex.ofReal_mul]; unfold closes; ring
  have hx : r i * r j * (WickK G).cov (spin G s i) (spin G s j)=(WickK G).cov i j := tendsto_nhds_unique_of_eventuallyEq ((islands G (spin G s i) (spin G s j)).const_mul _) (islands G i j) (Eventually.of_forall hp)
  simp only [scope,treats,signedM,Finsupp.linearCombination_single,Pi.smul_apply,smul_eq_mul]; rw [← hx]; unfold r; ring
end YM.XSpace
