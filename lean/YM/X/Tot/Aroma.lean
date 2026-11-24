import YM.X.Tot.Linear
/-!
# ledger script cost templates, health projections (down a given number of slots). All estimates anchored by true exterior only.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
-- Script convenience curvature. Cursor syntax let binder
variable (q:ℕ+)(x y z:Fielding.Walk) (χ:Floor R)
local notation "K"=> Billboard G q
local notation "Q"=> qu q G
variable (a b c:Tops G) (A B C': Billboard G q)(L : Weave q)
def pointScrim (a b c:Tops G): ℕ→ℂ:= camp q L (rise q c (rise q b A)) (rise q a B) C'+ camp q L (rise q c (rise q b A)) B (rise q a C')
abbrev mark₃ (a b c:Tops G):= vertexLift q (credit q a*(credit q b * credit q c))
abbrev Meters (A B C':Billboard G q)(a b c:Tops G): ℕ→ℂ:= camp q 1 (rise q a A) (rise q b B) (rise q c C')
lemma viz_triple (i:ℕ)(z:Site (side q i)): mark₃ q a b c i z=triple (Vane q a i (lift z)) (Vane q b i (lift z)) (Vane q c i (lift z)):= by unfold mark₃; rw [map_mul,map_mul];simp only [Pi.mul_apply,viz_credit]
lemma issued : mantle q L A B C' (mark₃ q a b c)= pointScrim q A B C' L a b c + pointScrim q A B C' L b a c + pointScrim q A B C' L c a b + camp q L (rise q c (rise q b (rise q a A))) B C':= by ext1 i; simp only [mantle,pointScrim,camp,crow,Pi.add_apply, Pi.mul_apply,vapor,viz_triple,calc_major,scrim,Finset.sum_add_distrib,mul_add, rise] -- need second simp sum after mul_add
lemma effective : relevant q A B C' (mark₃ q a b c)= Meters q A B C' a b c+Meters q A B C' a c b+ Meters q A B C' b a c+Meters q A B C' b c a+Meters q A B C' c a b+Meters q A B C' c b a:= by ext1 i; simp only [relevant,Meters,camp,crow,Pi.add_apply, Pi.mul_apply,one_mul,vapor,viz_triple,just_school,send,Finset.sum_add_distrib,mul_add, rise]
variable {T₁ T₂ T₃:Set ℕ}{B₁ B₂ B₃:Set (Marks G)}
def Core (k d l:ℕ)(P:ChaseR):Prop:= ∀ f g h:Foam G, f∈Page q (afterV T₁ k) B₁ → g∈Page q (afterV T₂ d) B₂→ h∈Page q (afterV T₃ l) B₃→ gather q x y z f g h∈P
-- implicit T sets must explicit parameters (goal `T₁:=...`) alias
local notation "K₁"=> Core q x y z (T₁:=T₁) (T₂:=T₂) (T₃:=T₃) (B₁:=B₁) (B₂:=B₂) (B₃:=B₃)
variable (X:A∈Slalom q x 0 T₁ B₁)(Y:B∈Slalom q y 0 T₂ B₂)(Z:C'∈Slalom q z 0 T₃ B₃)(P:ChaseR)(hP:Usual P)
lemma picked (h:A∈Slalom q x k (afterV T₁ k) B₁): rise q a A ∈Slalom q x (k+1) (afterV T₁ (k+1)) B₁:= by
    apply Eq.mp ?_ (pickS q _ _ x a A h); congr 1; rw [show afterV (afterV T₁ k) 1= afterV T₁ (k+1) from by ext1 z; simp [afterV,add_comm,add_left_comm,add_assoc]]
@[simp] lemma picked₁ (X:A∈ Slalom q x 0 T₁ B₁): rise q a A ∈Slalom q x 1 (afterV T₁ 1) B₁:= pickS q T₁ B₁ x a A X
lemma after0 (T:Set ℕ):afterV T 0=T:= by ext;simp [afterV]
local notation "D"=> (1-bend q χ x)
include X Y Z hP
variable (h:Geom q r x y z)(hq:1<q.val)(hr:R<r)
include h hq hr χ
lemma legal_I (he: K₁ 1 1 1 P): relevant q A B C' (mark₃ q a b c)∈P:= by
   rw [effective]; have he(a b c:Tops G): Meters q A B C' a b c∈P:= visit (B₁:=B₁) (B₂:=B₂) (B₃:=B₃) (T₁:=afterV T₁ 1) (T₂:=afterV T₂ 1) (T₃:=afterV T₃ 1) q x y z _ _ _ 1 P hP (picked₁ q x a _ X) (picked₁ q y b _ Y) (picked₁ q z c _ Z) (distinct_cost q x y z χ h hq hr) he
   repeat (first|apply Submodule.add_mem|exact he _ _ _)
lemma legal_M (h1:K₁ 3 0 0 P)(h2:K₁ 2 1 0 P)(h3:K₁ 2 0 1 P): mantle q D A B C' (mark₃ q a b c)∈P:= by
    rw [issued]; rw [Core,after0] at h1 h2 h3; rw [after0] at h1; -- `core` property implicit eq
    have Q₁(a b:Tops G): rise q b (rise q a A)∈Slalom q x 2 (afterV T₁ 2) B₁:= picked q x b _ (picked₁ q x a _ X)
    have hA(a b c:Tops G): pointScrim q A B C' D a b c∈P:= by refine Submodule.add_mem P (?_) (?_); exact visit q _ _ _ B₁ B₂ B₃ x y z _ _ _ _ P hP (Q₁ b c) (picked₁ q y a _ Y) Z (two_roof q x y z χ h hq hr) h2; exact visit q _ _ _ B₁ B₂ B₃ x y z _ _ _ _ P hP (Q₁ b c) Y (picked₁ q z a _ Z) (two_roof' q x y z χ h hq hr) h3
    refine (P.add_mem (P.add_mem (P.add_mem (hA a b c) (hA _ _ _)) (hA _ _ _)) ?_); exact visit q _ _ _ B₁ B₂ B₃ x y z _ _ _ _ P hP (picked q x c _ (Q₁ a b)) Y Z (three_roof q x y z χ h hq hr) h1
end YM.PositionX.Tot
