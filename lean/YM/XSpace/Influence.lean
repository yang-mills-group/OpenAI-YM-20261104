import YM.Next.MAXWELL.Canopy
import YM.Next.MAXWELL.Ends
import YM.Next.MAXWELL.Depth
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n :ℕ}

abbrev Sec (G:Gauge) (d:ℕ) := ↥(shellSector G d)
instance Sec_fd (d:ℕ): FiniteDimensional ℂ (Sec G d):= by unfold Sec shellSector; infer_instance
instance Sec_fr (d:ℕ): FiniteDimensional ℝ (Sec G d):= Module.Finite.trans ℂ _

def coeS (d:ℕ) := (shellSector G d).subtype
def ori (s:Ortho) (d:ℕ): Module.End ℂ (Sec G d):= LinearMap.codRestrict (shellSector G d) ((reflectPol s).toLinearMap ∘ₗ coeS d) (fun x=> (closed_sector x.property s).1)
lemma val_ori (s:Ortho) (x:Sec G d): (ori s d x).val=reflectPol s x.val:=rfl
def reel (d:ℕ): Sec G d →ₛₗ[starRingEnd ℂ] Sec G d where
  toFun x:= ⟨realForm x.val,(closed_sector x.property 1).2⟩
  map_add' _ _:=Subtype.ext (_root_.map_add ..)
  map_smul' _ _:=Subtype.ext (real_scale ..)
lemma real_proj (x:Sec G d) : (reel d x).val=realForm x.val:=rfl
lemma reel_back (x:Sec G d): reel d (reel d x)=x:= by apply Subtype.ext; apply equalPol; intro V; simp_rw [real_proj,real_eval,star_star]
lemma reel_scale (x:Sec G d) (a:ℝ): reel d (a • x)=a • reel d x:=by
  have he (x : Sec G d): a • x=(a:ℂ) • x:=Subtype.ext (volumes _ _ |>.symm)
  rw [he x, (reel d).map_smulₛₗ,show (starRingEnd ℂ) (a:ℂ)=(a:ℂ) by simp,he (reel d x)]
def leaf (G:Gauge) (d:ℕ) : Sec G d:= ⟨1,unit_fits (unit_mem _)⟩
def Change (G :Gauge) (d:ℕ): Submodule ℝ (Module.End ℂ (Sec G d)) where
  carrier:= {T| T (leaf G d)=0 ∧ (∀ l ≤ d,∀ p:Sec G d,p.val∈ shellSector G l→ (T p).val∈ shellSector G l) ∧
    (∀ p,T (reel d p)=reel d (T p)) ∧ ∀ (s:Signed) p,T (ori s.ortho d p)=ori s.ortho d (T p)}
  zero_mem':=⟨rfl,fun _ _ _ _=>Submodule.zero_mem _,fun _=> (map_zero _).symm,fun _ _=>(map_zero _).symm⟩
  add_mem' := by
    rintro T U ⟨h,h1,h2,h3⟩ ⟨f,f1,f2,f3⟩; exact ⟨by simp only [LinearMap.add_apply,h,f,zero_add],fun l hl p hp=>Submodule.add_mem _ (h1 l hl p hp) (f1 l hl p hp),fun p=> by rw [LinearMap.add_apply,h2,f2,LinearMap.add_apply,map_add],fun s p=> by rw [LinearMap.add_apply,h3,f3,LinearMap.add_apply,map_add]⟩
  smul_mem' := by
    rintro b T ⟨h,h1,h2,h3⟩; refine ⟨by rw [LinearMap.smul_apply,h,smul_zero],fun l hl p hp=> ((shellSector G l).restrictScalars ℝ).smul_mem b (h1 l hl p hp),fun p=> ?_,fun s p=>?_⟩
    · rw [LinearMap.smul_apply,h2,LinearMap.smul_apply,reel_scale]
    rw [LinearMap.smul_apply,h3,LinearMap.smul_apply]; exact (_root_.map_smul ((ori s.ortho d).restrictScalars ℝ) b _).symm

instance Change_addgrp (G:Gauge) (d:ℕ): AddCommGroup ↥(Change G d):= @Submodule.addCommGroup ℝ (Module.End ℂ (Sec G d)) _ _ _ (Change G d)
instance finite_changes (G:Gauge) (d:ℕ): FiniteDimensional ℝ (Change G d):=by
  letI : FiniteDimensional ℝ (Module.End ℂ (Sec G d)):= Module.Finite.trans ℂ _
  exact FiniteDimensional.of_injective (V₂:=Module.End ℂ (Sec G d)) (Change G d).subtype Subtype.val_injective

end YM.XSpace.Normalize
