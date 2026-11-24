import YM.FormalOPE.RG10.MultiGauge.Degree
/-!
 # integrating a spinning polynomial over part of its slots yields a coherent polynomial
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory Measure PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F K : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]
 [NormedAddCommGroup K][NormedSpace ℝ K]
namespace Papers
variable (u:F→ₗ[ℝ] E)(k:E)
 def relocate : Permit E →ₐ[ℝ] Permit F where
  toFun a:=⟨fun x=> a.val (u x+k),consign u _ a.property⟩
  map_zero':= rfl
  map_one':= rfl
  map_mul' _ _:=rfl
  map_add' _ _:=rfl
  commutes' _:=rfl
 def translation (g:F→ₗ[ℝ] E): Permit E →ₐ[ℝ] Permit F where
  toFun a:=⟨a.val ∘ g, pull g a.property⟩
  map_zero':= rfl
  map_one':= rfl
  map_mul' _ _:=rfl
  map_add' _ _:=rfl
  commutes' _:=rfl
 def left : Permit E →ₐ[ℝ] Permit (E × F):= translation (LinearMap.fst ℝ E F)
 def right : Permit F →ₐ[ℝ] Permit (E × F):= translation (LinearMap.snd ℝ E F)
 def loom (a:Permit E)(b:Permit F): Permit (E × F):= left a * right b
lemma loom_mul (a c:Permit E)(b d:Permit F): loom a b * loom c d=loom (a*c) (b*d):= by simp_rw [loom,map_mul]; ring

def needle : Set (Permit (E×F)):= Set.range fun (a:Permit E × Permit F)=> loom a.1 a.2
def stitch : Submodule ℝ (Permit (E×F)):= Submodule.span ℝ needle
lemma needle_point (a:Permit E)(b:Permit F): loom a b ∈ stitch:= Submodule.subset_span ⟨(a,b),rfl⟩
lemma dual_stitch {a b:Permit (E × F)} (h:a∈stitch)(k:b∈stitch): a*b∈stitch:=by
 change LinearMap.mul ℝ (Permit (E × F)) a b∈ stitch
 apply LinearMap.BilinMap.apply_apply_mem_of_mem_span stitch needle needle (LinearMap.mul ℝ (Permit (E×F))) _ _ _ h k
 rintro i ⟨⟨a,b⟩,rfl⟩ j ⟨⟨c,d⟩,rfl⟩; change loom a b * loom c d∈ stitch; rw [loom_mul]; exact needle_point (a*c) (b*d)
-- use unbundled induction
lemma integral_plan (a:Permit (E × F)):a ∈ stitch:= by
 let P (f:E×F → ℝ):= ∃ b∈ stitch,b.val=f
 have he:P a.val:=by
  apply induction (P:=P) _ _ _ _ a.property
  · intro ℓ
    let f:= ℓ.comp (LinearMap.inl ℝ E F); let g:=ℓ.comp (LinearMap.inr ℝ E F)
    let b:=loom (⟨f,linear f⟩:Permit E) (1:Permit F); let c:= loom (1:Permit E) (⟨g,linear g⟩:Permit F)
    refine ⟨b+c,stitch.add_mem (needle_point _ _) (needle_point _ _),?_⟩; funext ⟨x,y⟩; change ℓ (x,0)*1 + 1*ℓ (0,y)=ℓ (x,y); simp only [mul_one,one_mul,←_root_.map_add]; simp
  · intro x; refine ⟨loom (⟨fun _=>x,fixed _⟩:Permit E) (1:Permit F),needle_point _ _,?_⟩; funext y; exact mul_one _
  · rintro _ _ _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩; exact ⟨a+b,stitch.add_mem ha hb,rfl⟩
  rintro _ _ _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩; exact ⟨a*b,dual_stitch ha hb,rfl⟩
 obtain ⟨b,hb,hc⟩:=he; exact Subtype.ext hc ▸ hb
 def froze (y:F) : Permit (E×F)→ₐ[ℝ] Permit E:= relocate (LinearMap.inl ℝ E F) (0,y)
lemma froze_at (y:F)(a: Permit (E × F))(x:E): (froze y a).val x=a.val (x,y):= by change a.val ((x,0)+(0,y))=_; simp
lemma froze_loom (y:F)(a:Permit E)(b:Permit F): froze y (loom a b)= (b.val y) • a := by
 apply Subtype.ext; ext1 x; rw [froze_at]; exact mul_comm (a.val x) (b.val y)
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable (Λ:Law E)(μ:Measure E)[IsAddHaarMeasure μ]
 def shell : Permit (E×F) →ₗ[ℝ] (F→ℝ):= LinearMap.pi fun y=> (opening μ Λ).comp (froze y).toLinearMap
lemma covered (a:Permit (E×F)): shell Λ μ a∈ papers F:= by
 induction integral_plan a using Submodule.span_induction with
 | mem x h=>
   obtain ⟨⟨a,b⟩,rfl⟩:= h
   rw [show shell Λ μ (loom a b)= b.val * fun _=> opening μ Λ a from funext fun x=> by
       change opening μ Λ (froze x (loom a b))=_; rw [froze_loom, map_smul]; rfl]
   exact (papers F).mul_mem b.property (fixed _)
 | zero=> rw [map_zero]; exact (papers F).zero_mem
 | add=> rw [map_add]; exact (papers F).add_mem (by assumption) (by assumption)
 | smul=> rw [map_smul]; rename_i r x h hh; exact (papers F).smul_mem hh r

 def splitting : Permit (E × F) →ₗ[ℝ] Permit F:= LinearMap.codRestrict (Subalgebra.toSubmodule (papers F)) (shell Λ μ) (fun a=> covered Λ μ a)
lemma singly : splitting Λ μ (F:=F) 1=1:= by apply Subtype.ext; funext y; change opening μ Λ (froze y 1)=1; rw [map_one,starts]
lemma Penn (a:Permit (E × F))(y:F): (splitting Λ μ a).val y = Λ.average μ (fun x=> a.val (x,y)):= by change Λ.average μ (froze y a).val=_; rw [funext (froze_at y a)]
end Papers
end YM.FormalOPE.RG10.MultiGauge
