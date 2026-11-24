import YangMills.WilsonProof.NativeSupport.YM.MS.Class.Common
/-!
# Convenient polynomial testing with H sign action
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open scoped Topology ContDiff InnerProductSpace
abbrev rform (j:ℕ) (f : FourP→ℂ):= Shape f (j:ℤ)
def spike (i:Axis): FourP:= Pi.single i 1
@[simp] lemma spike_self (i:Axis): spike i i=1:= by simp [spike]
@[simp] lemma spike_of_ne {i j:Axis} (h:j≠i): spike i j=0:= by simp [spike,h]
lemma slam (p : FourP) : ∑ i:Axis,p i • spike i=p:= by
   ext i; rw [Finset.sum_apply,Finset.sum_eq_single i]; simp
   · intro _ _ hx; simp [hx.symm]
   simp
-- signed path action; permutations and mirrors.
def down : Signed := ⟨Equiv.refl _,fun _=> true⟩
def turn (i j:Axis) : Signed:= ⟨Equiv.swap i j,fun _=> false⟩
def orient (f : Axis≃Axis): Signed:= ⟨f,fun _=> false⟩
@[simp] lemma down_act (p : FourP): down.act p= -p:= by ext; simp [Signed.act,down]
@[simp] lemma sign_go (s : Signed) (i:Axis): s.act (spike i)= if s.flip i then -spike (s.perm i) else spike (s.perm i):= by
   split_ifs with h <;> (ext j; obtain ⟨j,rfl⟩ := s.perm.surjective j; by_cases he:j=i; subst j; simp [h]; rw [Signed.act_at]; simp [he,s.perm.injective.ne he])
@[simp] lemma down_perm : down.perm=Equiv.refl _:=rfl
@[simp] lemma turn_act (i j:Axis) (p:FourP) (k : Axis) : (turn i j).act p k = p (Equiv.swap i j k):= by simp [Signed.act,turn]
@[simp] lemma mirror_act (i j : Axis) (p : FourP): (Signed.mirror i).act p j = if i=j then -p j else p j:= by simp [Signed.act,Signed.mirror,eq_comm]
lemma mirror_unmoved (i:Axis) (p:FourP) (h:p i=0): (Signed.mirror i).act p=p:= by ext; rw [mirror_act]; split <;> (subst_vars; simp [h])
lemma perm2 (i j a b:Axis) (h1:i≠j) (h2:a≠b) : ∃ f:Axis≃Axis, f i=a ∧ f j=b:= by
   let Q:=Equiv.swap i a; have hg : Q j≠ a:= by rw [← show Q i=a from Equiv.swap_apply_left ..]; exact Q.injective.ne h1.symm
   refine ⟨Q.trans (Equiv.swap (Q j) b),?_,Equiv.swap_apply_left ..⟩
   simp only [Equiv.trans_apply,show Q i=a from Equiv.swap_apply_left ..]; exact Equiv.swap_apply_of_ne_of_ne hg.symm h2

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : F→ℂ}
lemma shape_constant (h : Shape p 0) (x:F): p x=p 0:= Eq.symm (by simpa using h.scale 0 x)
lemma shape_linear (h : Shape p 1) : ∃ f:F→L[ℝ]ℂ, p=f := by
    let A:= coeff p 1 0; refine ⟨continuousMultilinearCurryFin1 ℝ F ℂ A,?_⟩
    funext x; exact congr_fun (Shape.form (j:=1) h) x -- argument named?
lemma shape_two (h : Shape p 2) : ∃ f:F→ₗ[ℝ] F→ₗ[ℝ] ℂ, (∀ x, p x=f x x) ∧ (∀ x y, f x y=f y x):= by
   let A:=Tensor.coeff p 2 0
   let U : F →ₗ[ℝ] F→ₗ[ℝ] ℂ:= LinearMap.mk₂ ℝ (fun x y=> (continuousMultilinearCurryFin1 ℝ F ℂ (A.curryLeft x)) y) (fun x y z=>by rw [map_add,map_add,_root_.add_apply]) (fun c x y=>by rw [map_smul,map_smul,_root_.smul_apply]) (fun _ _ _=> map_add ..) (fun _ _ _=> map_smul ..)
   have hz x y : U x y=A ![x,y]:= by
      change A (Fin.cons x (fun _ : Fin 1=> y))=_; congr 1; ext i; fin_cases i <;> rfl
   have he : p= Tensor.diagonal A:= Shape.form h
   refine ⟨U,?_,fun x y=>?_⟩
   · intro x; rw [he,hz]; unfold Tensor.diagonal; congr 1; ext i; fin_cases i <;> rfl -- he recursion?
   rw [hz,hz]; unfold A; rw [← coeff_symm (j:=2) (f:=p) (h.smooth.contDiffAt.of_le (by norm_cast)) ![x,y] (Equiv.swap 0 1)]; congr 1; ext i; fin_cases i <;> simp
lemma skew_null (c : ℂ) (e:c= -c): c=0:= by
    linear_combination (norm:=ring_nf) e / 2
lemma unstuck {F: FourP→ℂ} {i:Axis} (h : ∀ p, F ((Signed.mirror i).act p)= - F p) (p:FourP) (hp:p i=0) : F p=0:= skew_null _ (by simpa only [mirror_unmoved i p hp] using h p)
lemma shape_skew_one {F: FourP→ℂ} {i:Axis} (h: rform 1 F) (hv : ∀ p:FourP, F ((Signed.mirror i).act p)= -F p) : ∀ (p: FourP), F p=(p i:ℂ)*F (spike i) := by
   intro p; obtain ⟨L,hL⟩:= shape_linear h; rw [hL]; let q:=p-p i • spike i
   have hq : L q=0:= by rw [← show F q=L q from congr_fun hL q]; exact unstuck hv q (by unfold q; simp)
   conv_lhs=> arg 2; rw [show p=q+p i • spike i from (sub_add_cancel ..).symm]
   rw [map_add,map_smul,hq,zero_add,Complex.real_smul];
lemma shape_skew_two {F : FourP→ℂ} {i j:Axis} (h1:i≠j) (h:rform 2 F)
    (hv : ∀ p:FourP, F ((Signed.mirror i).act p)= -F p)
    (hh : ∀ p:FourP, F ((Signed.mirror j).act p)= -F p) : ∀ p:FourP, F p=(p i:ℂ)*(p j:ℂ)*F (spike i+spike j):= by
    intro p; obtain ⟨U,hq,hs⟩:=shape_two h
    let a:= p i • spike i; let b:= p j • spike j; let r:=p-a-b; have he : p= (a+b)+r:= by unfold r; abel
    have hx x y: F (x+y)=F x+2*U x y+F y:= by rw [hq,hq,hq]; simp only [map_add, LinearMap.add_apply,hs y]; ring
    -- conflict hx var rename
    have h0 : F r=0:= unstuck hv _ (by unfold r a b; simp [h1])
    have hA : F (a+r)=0:= unstuck hh _ (by unfold r a b; simp)
    have hB : F (b+r)=0:= unstuck hv _ (by unfold r a b; simp [h1])
    have hI : F a=0:= unstuck hh a (by unfold a; simp [h1.symm]); have hJ : F b=0:= unstuck hv b (by unfold b; simp [h1]);
    conv_lhs => rw [he,hx,hx]
    rw [hx (spike i),unstuck hh (spike i) (by simp [h1.symm]),unstuck hv (spike j) (by simp [h1]), map_add,LinearMap.add_apply,hI,hJ,h0]
    rw [hx,hI,h0] at hA; rw [hx,hJ,h0] at hB
    have hq : U a b=(p i:ℂ)*(p j:ℂ)*U (spike i) (spike j):= by unfold a b; simp only [map_smul,LinearMap.smul_apply]; simp; ring
    rw [hq]; linear_combination hA+hB
end YM.MS.Landau.Detect
