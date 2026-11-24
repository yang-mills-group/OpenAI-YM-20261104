import YM.Comparison.RG02.Moving.Rotation
import YM.Comparison.RG02.Affinity.Identity
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix PertExtension.Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E" => House X I

namespace Field
variable (C : Field X I)

local notation "Q₀"=> C.Q 0

def qarg (y:E) : Regulator X := (y.1,y.2.1)
def logarithm (s : Regulator X) := (Real.log (C.Q s).det - Real.log (Q₀).det)/2
def fluctuation (y:E) := y.1^2 * C.logarithm (qarg y)
def extra (y:E) := ((y.2.2) ⬝ᵥ ((C.gram (qarg y) - C.gram 0) *ᵥ y.2.2)) /2
def retax (f : E → ℝ) := f-C.extra-C.fluctuation

lemma pays_one : GradeAt 3 C.fluctuation := by
   have ht := GradeAt.shifts (fun y:E=> y.1) contDiffAt_fst rfl 2
   have he : ContDiffAt ℝ ω (fun y:E=> C.logarithm (qarg y)) 0 := ((((YM.Push.Loops.logdet_contDiff C.smooth (IsUnit.mk0 _ C.flat.det_pos.ne')).sub contDiffAt_const).div_const 2 : ContDiffAt ℝ ω C.logarithm 0).comp (f:=qarg) (0:E) (contDiffAt_fst.prodMk contDiffAt_snd.fst))
   exact ht.mul (GradeAt.anchored he (show C.logarithm _=0 by rw [logarithm,show qarg (0:E)=0 from rfl,sub_self,zero_div]))

lemma pays_two : GradeAt 3 C.extra := by
   let f : E→ Matrix I I ℝ := fun z=> C.gram (qarg z)-C.gram 0
   let g (i:I) := fun z:E=> z.2.2 i
   have ht (i j : I) : GradeAt 1 (fun z:E=> f z i j):= by
     have h := (C.gram_known.comp (f:=qarg) _ (show ContDiffAt ℝ ω (qarg (X:=X) (I:=I)) (0:E) from contDiffAt_fst.prodMk contDiffAt_snd.fst)).sub (g:=fun _=>C.gram 0) contDiffAt_const
     exact GradeAt.anchored (YM.Push.Loops.matrix_component h i j) (by simp [f,show qarg (0:E)=0 from rfl])
   have hh (i:I) : GradeAt 1 (g i):= GradeAt.anchored ((contDiffAt_apply ℝ ℝ i _).comp (f:=fun y:E=> y.2.2) 0 contDiffAt_snd.snd) rfl
   have hz := GradeAt.list_sum Finset.univ (fun i:I=> fun z:E=> g i z * ∑ j:I, f z i j * g j z) (fun i _ => (hh i).mul (GradeAt.list_sum Finset.univ _ (fun j (_ : j∈(Finset.univ:Finset I))=> (ht i j).mul (hh j))))
   refine (GradeAt.scale hz (GradeAt.unchecked (f:=fun _:E=> (2:ℝ)⁻¹) contDiffAt_const)).depends ?_
   exact Eventually.of_forall fun y=> by simp [extra,f,g,dotProduct,mulVec,div_eq_mul_inv]

variable {f : House X I → ℝ}
lemma keeps (hf : GradeAt 2 f) (y:E) : Assembly.jet (C.retax f) 2 y = Assembly.jet f 2 y := by
   unfold retax Assembly.jet; rw [iteratedFDeriv_sub_apply (((hf.sub (C.pays_two.lower (by decide))).smooth).of_le le_top) (C.pays_one.smooth.of_le le_top), iteratedFDeriv_sub_apply (hf.smooth.of_le le_top) (C.pays_two.smooth.of_le le_top), C.pays_one.vanish 2 (by decide), C.pays_two.vanish 2 (by decide), _root_.sub_zero, _root_.sub_zero]
lemma upholds (hf : Ray Q₀ f) : Ray Q₀ (C.retax f) := ⟨(hf.root.sub (C.pays_two.lower (by omega))).sub (C.pays_one.lower (by omega)),fun x v=> by simp_rw [C.keeps hf.root]; exact hf.quadratic x v⟩

variable (x:X) [FiniteDimensional ℝ X]
def link (t:ℝ) := C.B (t,t • x)
def vibe : Vibe X I := ⟨fun _=>0,C.B,GradeAt.grade_zero _,C.B_smooth,C.B_flat⟩
lemma outgoing (v:I→ℝ) (t:ℝ) : Affinity.Vibe.outreach x C.vibe t v= C.link x t *ᵥ v := by simp [Affinity.Vibe.outreach,Affinity.Vibe.basis,Affinity.Vibe.shifter,link,vibe]
variable {t:ℝ}
lemma paired (he : (C.link x t).transpose*C.gram (t,t • x)*(C.link x t)=C.gram 0) (h : 0 < (C.link x t).det) : C.logarithm (t,t • x)= Real.log (C.link x t).det := by
   rw [logarithm,C.paid_D he h,Real.log_mul C.flat.det_pos.ne' (pow_pos h 2).ne',Real.log_pow]; push_cast; ring
variable (ht : t≠0) (Z : Vibe X I)
variable (he : (C.link x t).transpose*C.gram (t,t • x)*(C.link x t)=C.gram 0) (hv : 0 < (C.link x t).det)
  {l : Hot R→ℕ} {F : Hot R→House X I→ℂ} (hf : Ray (C.Q 0) f)
include he hv hf ht

lemma charges (v:I→ℝ) : Radial.higher (C.vibe.price f) t (season x v)=Radial.higher (C.retax f) t (season x (C.link x t *ᵥ v)) := by
   let N:= C.link x t; let z:= N *ᵥ v; let y := season x z
   rw [Affinity.Vibe.enacted x C.vibe _ ht hf,outgoing]
   change Radial.higher f t y + force Q₀ v / 2 - force Q₀ z / 2 + Real.log N.det = _
   have hp (w:I→ℝ) : t • season x w= (t,t • x, t • w) := by rw [facing]; exact Prod.ext (mul_one t) rfl
   have hh (w:I→ℝ) (N:Matrix I I ℝ) : (t • w) ⬝ᵥ (N *ᵥ (t • w))= t^2*(w ⬝ᵥ (N *ᵥ w)) := by rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; ring
   have hu : C.extra (t • y)= (t^2)*(force Q₀ v - force Q₀ z)/2 := by
      unfold y extra; rw [hp]; dsimp only;
      rw [hh,Matrix.sub_mulVec,dotProduct_sub, ← C.force_lives he]; rfl
   have hz : C.fluctuation (t • y)=(t^2)*Real.log N.det := by unfold fluctuation y; rw [hp]; dsimp only; rw [show qarg (t,t • x,t • z)=(t,t • x) from rfl,paired C x he hv]
   change _= Radial.higher (C.retax f) t y
   unfold Radial.higher; simp_rw [← Assembly.jet_eq]; rw [keeps C hf.root]; unfold retax; simp only [Pi.sub_apply,hu,hz]; field_simp; ring

-- the Q-pump charge is *inside* the gaussian change. No unpaired moving scalar read.
variable [Fintype V]
local notation "P" => Assembly.numeric l F (C.retax f)
local notation "B" => Assembly.numeric l (fun i=> F i ∘ C.vibe.effect) (C.vibe.price f)
theorem present (v:I→ℝ) : P t (season x (C.link x t *ᵥ v))= B t (season x v) := by
   unfold Assembly.numeric; rw [C.charges x ht he hv hf v, Affinity.Vibe.marks R x C.vibe _ ht, outgoing]

theorem within (A : Set (I→ℝ)) :
    let p:= A.indicator (P t ∘ season x)
    let u:= ((fun v:I→ℝ=> C.link x t *ᵥ v) ⁻¹' A).indicator (B t ∘ season x)
    (Good (cloud (C.Q (t,t • x))) p ↔ Good (cloud Q₀) u) ∧ charge (cloud Q₀) u=charge (cloud (C.Q (t,t • x))) p := by
   intro p u
   have hz (i:R.Mode) : (atMark i p ∘ (fun v:I→ℝ=> C.link x t *ᵥ v))= atMark i u := by
      funext v; by_cases h : C.link x t *ᵥ v ∈ A <;> simp [p,u,atMark,Function.comp_def,h]
      exact (by simpa [Function.comp_def] using! congrArg (Marker.Poly.part · i) (C.present (F:=F) (l:=l) x ht he hv hf v))
   have hh (i:R.Mode) := C.port he hv (atMark i p)
   refine ⟨forall_congr' (fun i=> ?_),?_⟩
   · rw [← hz]; exact (hh i).1
   ext i; rw [components,components,← hz]; exact (hh i).2.symm

end Field
end YM.Comparison.RG02.Moving
