import YM.FormalBulk08.Flat.Plans
import YM.FormalBulk08.Jets.Caps

/-! Actual finite-period log variables, alive on the absolute slice. Need complex
Stationary invoices only in the later infinite calculation. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Work.F05 Stationary Tree
open Series Jets Wick Orb
open scoped Topology BigOperators Matrix ContDiff
variable {G : Gauge} {K : KernelChoices} {c f : Side} {S : StepData c f}

abbrev wire (G : Gauge) (c : Side) := Lines G c 1
abbrev Pine (G : Gauge) (S : StepData c f) (F : Forest S.ratio) := Flat.Alive G S F

def knot (F : Forest S.ratio) (i : F.Free) (a : G.ColorIndex) : Pine G S F := ⟨(i.val.1,coord i.val.2,a), by change (i.val.1,axisEquiv.symm (axisEquiv _))∉_; rw [axisEquiv.symm_apply_apply]; exact i.property⟩
def pines (F : Forest S.ratio) : F.Free × G.ColorIndex ≃ Pine G S F where
    toFun i:=knot F i.1 i.2
    invFun x := (⟨(x.val.1,axisEquiv.symm x.val.2.1),x.property⟩,x.val.2.2)
    left_inv := by rintro ⟨i,a⟩; simp only [knot]; congr; simp only [show coord _=axisEquiv _ from rfl,axisEquiv.symm_apply_apply]
    right_inv x := by
       apply Subtype.ext; dsimp only [knot]
       rw [show coord _=_ from axisEquiv.apply_symm_apply _]
lemma knot_symbol (F : Forest S.ratio) (u : F.Free) (k:G.ColorIndex) : pines F (u,k)= knot F u k:=rfl

variable (G)
def stand (F : Forest S.ratio) : Rays (Pine G S F) ≃L[ℝ] AxisChart G F := LinearEquiv.toContinuousLinearEquiv {
   toFun a i:= WithLp.toLp 2 fun j=> a (pines F (i,j))
   invFun z x:= z ((pines F).symm x).1 ((pines F).symm x).2
   map_add' a b:= rfl
   map_smul' a b:= rfl
   left_inv a := funext fun i=>by
      change a (pines F (_,_))=a i; exact congr_arg _ ((pines F).apply_symm_apply i)
   right_inv z := by ext i b; simp only [Equiv.symm_apply_apply] }

def offer (F : Forest S.ratio) : Rays (Pine G S F)→L[ℝ] Rays (wire G f) := LinearMap.toContinuousLinearMap (Flat.dropRoot G S F)ᵀ.mulVecLin
lemma offer_as (F : Forest S.ratio) (x : Rays (Pine G S F)) : offer G F x=(Flat.dropRoot G S F)ᵀ*ᵥ x := rfl
lemma sips (F : Forest S.ratio) (x : Rays (Pine G S F)) : input G f (offer G F x) = F.drape (exposure F 0 (stand G F x)) := by
   funext i; rw [input,Work.F03.represent_link]; by_cases h : i∈F.trunks
   · have he : (arm G f 1 (offer G F x)) (i.1, coord i.2)=0 := by
        ext a; change ((Flat.dropRoot G S F)ᵀ *ᵥ x) (i.1, coord i.2,a)=0; exact Flat.bring_dead F x (by change ¬ (i.1,axisEquiv.symm (axisEquiv _))∉_; simp only [Equiv.symm_apply_apply]; exact Classical.not_not.mpr h)
     rw [he, show F.drape _ i=1 from F.on_tree _ ⟨i,h⟩]; simp
   let u:F.Free:= ⟨i,h⟩
   have he : (stand G F x) u = (arm G f 1 (offer G F x)) (i.1, coord i.2) := by ext a; exact (Flat.bring_alive F x (pines F (u,a))).symm
   rw [show F.drape _ i=exposure F 0 (stand G F x) u from F.off_tree _ u,exposure,he,link_one,replica_one,Pi.one_apply,mul_one]

end YM.FormalBulk08.Reef
