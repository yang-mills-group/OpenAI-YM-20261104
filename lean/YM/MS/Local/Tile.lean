import YM.MS.RayRules
import YM.MS.Roles
/-!
# Envelope spaces and local polynomials of pure grade

Used for the continuum free BV classification with insertions (NO integration
by parts at mark). Statements are independent of gauge selection etc. Use total
momentum grading and a separate charge grading (`w` and `c`). Terms need not be
symmetric until applying closure to them. First prove necessity/sufficiency of
independent-one-factor span on each homogeneous direction chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open scoped Topology ContDiff
variable {A E P : Type} {p : Sector A} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
variable (w c : A→ℤ) (P) (h q : ℤ) (r : ℕ)
abbrev Atom (A:Type) (P:Type) := Mode A P
abbrev Twig (A:Type) (P:Type) := Atom A P → ℂ
variable {P}
structure Star (f : Twig A P) : Prop where
    form a : Shape (fun p=>f (a,p)) (h-w a)
    real' i:c i.1≠q→ f i=0
variable (P)
def seed : Submodule ℂ (Twig A P) where
    carrier := setOf fun f=> Star w c h q f
    zero_mem':= ⟨fun _ => form_zero _,fun _ _=> rfl⟩
    add_mem' {x y} hx hy:= ⟨fun a => ((mem_setOf.mp hx).form a).add ((mem_setOf.mp hy).form a), fun i he=> by simp [ (mem_setOf.mp hx).real' i he,(mem_setOf.mp hy).real' i he]⟩
    smul_mem' k x hx:= ⟨fun a=> ((mem_setOf.mp hx).form a).scalar k, fun i he=> by simp [(mem_setOf.mp hx).real' i he]⟩

variable {P}
structure Cub (f : Row A P ℂ) : Prop where
   shape : Form f w h false
   tag v: fieldDim c v≠q → f v=0
   rank v: List.length v≠ r→ f v=0
variable (P)
def tile : Submodule ℂ (Row A P ℂ) where
    carrier := setOf (Cub w c h q r)
    zero_mem':= ⟨Form.zero, fun _ _=>rfl,fun _ _=>rfl⟩
    add_mem' {x y} hx hy:= ⟨(mem_setOf.mp hx).shape.add (mem_setOf.mp hy).shape,
      fun i he=> by simp [ (mem_setOf.mp hx).tag i he,(mem_setOf.mp hy).tag i he],fun i he=> by simp [(mem_setOf.mp hx).rank i he,(mem_setOf.mp hy).rank i he]⟩
    smul_mem' k x hx:= ⟨(mem_setOf.mp hx).shape.scalar k, fun i he=> by simp [(mem_setOf.mp hx).tag i he], fun i he=> by simp [(mem_setOf.mp hx).rank i he]⟩
-- order of args `w c P?`
variable {P w c h q r} -- A implicit update
lemma seedStar {f : Twig A P}: f∈ seed (A:=A) (w:=w) (c:=c) P h q ↔ Star w c h q f := Iff.rfl
lemma tileCub {f : Row A P ℂ} : f ∈ tile (A:=A) (w:=w) (c:=c) P h q r ↔ Cub w c h q r f:= Iff.rfl

section bud
-- simple tensor `rank=1 letter f` times `g` as ordered tensor. Not shuffle. Need calculus separate.
def bud (f : Twig A P) (H : Row A P ℂ) : Row A P ℂ
    | []=>0
    | i::w => f i * H w
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] lemma bud_cons (f : Twig A P) (H : Row A P ℂ) (i : Mode A P) (w) : bud f H (i::w)= f i * H w:=rfl
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] lemma bud_nil (f : Twig A P) (H : Row A P ℂ): bud f H []=0:=rfl

def place (A P:Type) : Twig A P →ₗ[ℂ] Row A P ℂ →ₗ[ℂ] Row A P ℂ := LinearMap.mk₂ ℂ bud (fun i j k=> funext fun x=> by cases x <;> simp [add_mul]) (fun c i j=> funext fun x=> by cases x <;> simp [mul_assoc]) (fun i j k=> funext fun x=> by cases x <;> simp [mul_add]) (fun c i j=> funext fun x=> by cases x <;> simp [mul_left_comm])
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma place_at (f : Twig A P) (g : Row A P ℂ) : place A P f g=bud f g:= rfl
lemma enters {f : Twig A P} {g : Row A P ℂ} {b d : ℤ} (F : Star w c h q f) (G : Cub w c b d r g) : Cub w c (h+b) (q+d) (r+1) (bud f g) := by
   refine ⟨fun E _ _ u _=> ?_, fun i hi=>?_,fun i hi=>?_⟩
   · cases u with
     | nil=> exact form_zero _
     | cons a u =>
        have hg := G.shape E u (fun h=>Bool.noConfusion h)
        convert ((F.form a.1).linear a.2).mul hg using 1; rfl; rw [field_cons]; omega
   · cases i with
     | nil=> rfl
     | cons i u=> rw [bud_cons]; by_cases hx:c i.1=q; exact mul_eq_zero_of_right _ (G.tag u (by contrapose! hi; simp only [field_cons,hx,hi]))
                  exact mul_eq_zero_of_left (F.real' i hx) _
   cases i with
   | nil=> rfl
   | cons i u=> rw [bud_cons]; exact mul_eq_zero_of_right _ (G.rank u (by simpa using hi))
end bud
section sight
-- Canonical plane chart. Fin d carried here. Enough to reconstruct arbitrary ordered symbol values/vectors.
def gaze (g : Fin r→ A) (p: Fin r→ P) := List.ofFn fun i => (g i,p i)
def arr (a : Fin r→ A) : Wire A (Fin r → P) P := List.ofFn fun i:Fin r=> (a i,ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin r=>P) i)
lemma at_arr (a:Fin r→ A) (p:Fin r→P): sail (arr a) p=gaze a p:= by simp [sail,arr,gaze]; rfl
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma gaze_weight (g : Fin r→ A) (p : Fin r→P) : fieldDim w (gaze g p)=∑ i,w (g i):= by simp [fieldDim,gaze,Fin.sum_ofFn]
lemma arr_weight (g : Fin r→A) : fieldDim w (arr (P:=P) g)=∑ i,w (g i):= by simp [fieldDim,arr,Fin.sum_ofFn]
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma gaze_len (g : Fin r→ A) (p : Fin r→P): (gaze g p).length=r:=by simp [gaze]
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma discovered (l : Legs (Mode A P)) (hp:l.length=r): ∃ g : Fin r→A, ∃ p, l=gaze g p:= by
   subst r; refine ⟨fun i=> (l.get i).1, fun i=> (l.get i).2,?_⟩; simp [gaze]
lemma Cub.visible {f : Row A P ℂ} (H : Cub w c h q r f) (g : Fin r→ A) : Shape (fun p=> f (gaze g p)) (h-∑ i,w (g i)):= by
   convert H.shape _ (arr g) (fun h=> Bool.noConfusion h) using 1; · ext; rw [fieldVal,at_arr]
   rw [arr_weight]
end sight
end YM.MS.Local
