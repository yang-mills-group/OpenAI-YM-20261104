import YM.X.Tot.Choose
/-! # biome statements for emission occupancy and retirement cost. used with heights summing to $3$. Parameter core regular for ending tests ∗both released and tendsTo zero∗. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (q:ℕ+)
local notation "H"=> Hair G
local notation "Ψ"=> Billboard G q
local notation "Ω"=> Foam G
local notation "Fℕ"=>(atTop:Filter ℕ)
variable (T₁ T₂ T₃:Set ℕ)(B₁ B₂ B₃:Set (Marks G))(x y z:Fielding.Walk) (A B C:Billboard G q)
abbrev ChaseR := Submodule ℂ (ℕ→ℂ)
def Usual (P:ChaseR):Prop:= ∀ x y:ℕ→ℂ, Released x → y∈ P → x*y∈P
lemma usual_crew : Usual Shelf.crew:= fun _ _ h y=> breaths h y
lemma usual_fading : Usual (Shelf.fades ℂ):= by
   intro x y h ht; obtain ⟨c,hc⟩:=h; simpa only [mul_zero] using! (hc.mul (show Tendsto y atTop (𝓝 0) from ht)) -- goal may mem
local notation "Λ"=> Weave q
variable (L: Weave q)
def usable (p:Λ)(u v w:ℕ):Prop:= ∀ a b c:List (Marks G× Tops G),a.length=u → b.length=v → c.length=w →Released (crow q (p*arrows q x a*arrows q y b*arrows q z c))
abbrev qu (q:ℕ+)(G:Gauge):= fun i:ℕ=> flow G (side q i)
local notation "Q"=> (qu q G)
def vapor (A B C:Ψ): Λ:= fun i z=> tri ((qu q G) i) (A i z) (B i z) (C i z)
-- order of variable q implicit? 
def gather (x y z:Fielding.Walk)(A B C:Foam G): ℕ→ℂ:= fun i=>tri (Q i) (dress (x i) (A i)) (dress (y i) (B i)) (dress (z i) (C i))
lemma gaze (a b c:Weave q)(A B C:Foam G): vapor q (a • cloak q x A) (b • cloak q y B) (c • cloak q z C)= a*b*c*ensign q (gather q x y z A B C):= by
    ext1 i; ext1 z'; change tri _ (a i z' • _) (b i z' • _) (c i z' • _) =_; rw [tri_scale,tri_scale₁,tri_scale₂]; change a i z'*(b i z'*(c i z' * _))=a i z'*b i z'*c i z'*_; simp_rw [mul_assoc];rfl
lemma crowd_time (a:Weave q)(f:ℕ→ℂ): crow q (a*ensign q f)=crow q a*f:= by ext1 i; unfold crow ensign; simp_rw [Pi.mul_apply, ←Finset.sum_mul]; ring -- triv
lemma vapor_cycle : vapor q A B C=vapor q C A B:= by ext1 i; ext1 z; unfold vapor; exact tri_rotate (Q i) (A i z) (B i z) (C i z)
-- laws packaged for induction
abbrev camp (A B C:Ψ) := crow q (L*vapor q A B C)
local notation "S₀"=> camp q L
lemma pulse : camp q L A B C=camp q L C A B:= by unfold camp; rw [vapor_cycle (A:=A) (B:=B)] -- args
lemma burst (D:Ψ) : S₀ (A+D) B C= S₀ A B C + S₀ D B C:= by unfold camp; rw [show vapor q (A+D) B C=vapor q A B C+vapor q D B C from by ext1 i; ext1 z; simp only [vapor,Pi.add_apply]; exact tri_plus (Q i) (A i z) (B i z) (C i z) (D i z),mul_add,crowd_plus]
lemma cold : S₀ 0 B C=0:= by unfold camp; rw [show vapor q 0 B C=0 from by ext1 i; ext1 z; unfold vapor; simp,mul_zero]; funext i; simp [crow]
lemma biol (a:ℂ):S₀ (a • A) B C=a • S₀ A B C:= by unfold camp; rw [show vapor q (a • A) B C=a • vapor q A B C from by ext1 i; ext1 z; simp only [Pi.smul_apply,vapor]; exact tri_scale .., mul_smul_comm,crowd_scale]
lemma pulse' : S₀ A B C= S₀ B C A := Eq.symm (pulse ..)
-- uniform price via combining spans. no iterated recursion needed
variable (P:ChaseR)
lemma buy {D : Billboard G q}(h:D∈Slalom q x k T₁ B₁)(hp:∀(a:List (Marks G × Tops G))(p:Foam G), a.length=k→p∈Page q T₁ B₁ →camp q L (arrows q x a • cloak q x p) B C ∈ P) : camp q L D B C∈ P:= by
    induction h using Submodule.span_induction with
    | mem _ h=> obtain ⟨v,p,h,hx,rfl⟩:=h; exact hp v p h hx
    | zero=> rw [cold];exact P.zero_mem
    | add a b _ _ x y=> rw [burst];exact P.add_mem x y
    | smul a b _ h=> rw [biol]; exact P.smul_mem _ h
variable (hu: Usual P)
include hu
lemma visit (a:A∈ Slalom q x k T₁ B₁)(b:B∈ Slalom q y d T₂ B₂)(c:C∈ Slalom q z l T₃ B₃) (h:usable (G:=G) q x y z L k d l) (he:∀ A B C:Foam G,A∈ Page q T₁ B₁→ B∈ Page q T₂ B₂ → C∈ Page q T₃ B₃→ gather q x y z A B C∈P) : camp q L A B C∈ P:= by
    apply buy q T₁ B₁ x B C L P a; intro l' m₁ h₁ he₁; rw [pulse']; refine buy q T₂ B₂ y _ _ L P b ?_; intro l₂ m₂ h₂ he₂; rw [pulse']; refine buy q T₃ B₃ z _ _ L P c ?_; intro l₃ m₃ h₃ he₃; rw [pulse']; unfold camp; rw [gaze,← mul_assoc, crowd_time]; refine hu _ _ ?_ (he _ _ _ he₁ he₂ he₃); rw [←mul_assoc,← mul_assoc]; exact h _ _ _ h₁ h₂ h₃ -- move λ after brace
end YM.PositionX.Tot
