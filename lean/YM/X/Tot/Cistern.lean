import YM.X.Tot.Hem
/-!
# two-point gathering scarcity if helic same minus lines. No continuity assumption on Y regulator low-coefficients beyond paid emission. For snuff and Ward tangent. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k:ℕ} {V I:Type*} {r R:ℝ} {n:Side}
local notation "F₀"=> (fades ℂ)
variable (q:ℕ+)(χ:Floor R)
local notation "Q"=> qu q G
local notation "Ω"=> Foam G
variable (x y z:Fielding.Walk)(p p' a b: Foam G)(A B: Marks G)
local notation "Θ"=> (Reed.Horizontal G)
local notation "Gτ" => gather q x y z
def meets (q:ℕ+)(x y:Fielding.Walk)(A B: Marks G)(k:ℕ):= treats (qu q G k) (Vane q A k (x k)) (Vane q B k (y k))
lemma meets_sym : meets q x y A B= meets q y x B A:= by ext1 i; unfold meets; rw [treats_comm]
def utop (A:Marks G): Tops G:= ⟨A.k,A.x,A.order, Submodule.mem_top⟩
lemma meets_spend (k:ℕ): meets q x y A B k=entryK (side q k) (epsilon q k) (x k) A (y k) (utop B):= by apply stamps (e:=epsilon q k) (n:=side q k) (x k) (y k) A (utop B)
def supF (q:ℕ+)(x:Fielding.Walk)(b:Marks G)(k):= fromP q b.k x b.x k
def cohabit (q:ℕ+)(x y:Fielding.Walk)(B:Marks G)(P:Foam G):Foam G:= fun k=> stroke (supF q (y-x) B k) (P k)
lemma home_bp (n:Side)(f g:Fan G)(x y z:Cover): treats (flow G n) (com (leadsL x f)) (com (leadsL y g))=treats (flow G n) (com (leadsL (z+x) f)) (com (leadsL (z+y) g)):= by rw [cornered,cornered, ← spent,← spent, spend_lead]
lemma mate_prev (x:Cover)(n:Side)(u:Fan G)(p:Curly G): dress x (edge (flow G n) (com u) p)=edge (flow G n) (com (leadsL x u)) (dress x p):= by
   induction p using MvPolynomial.induction_on with
   | C x'=> simp_rw [edge, slit_C, map_zero,dress, rename_C,slit_C]
   | add p q h g=> simp_rw [map_add,h,g]
   | mul_X p i IH=>
       have hp : (X (R:=ℂ) i)=glyph (com (Finsupp.single i 1)):= by rw [com_text,blade,Finsupp.linearCombination_single,one_smul];
       rw [hp,map_mul (dress x),Derivation.leibniz,Derivation.leibniz]; simp only [smul_eq_mul,map_add,map_mul,IH, dress_glyph,link]; rw [dress,rename_C]; congr 3; simpa only [leads_zero, add_zero] using home_bp n u (Finsupp.single i 1) 0 0 x
lemma cohab (k:ℕ): edge (Q k) (Vane q A k (y k)) (dress (x k) (p k))= dress (x k) (cohabit q x y A p k):= by
   rw [cohabit,supF,fromP,←palette,mate_prev,Vane]; unfold tack; rw [map_smul,leads_comp]; simp
lemma mate_cons (l:List (Stool G)) : cohabit q x y A (textA q (B::l))= meets q y x A B • textA q l + credit q B * cohabit q x y A (textA q l):= by
    ext1 i; rw [text_cons]; let k:=i; let D:=dress (G:=G) (x i); have D_in : Injective D:= MvPolynomial.rename_injective (R:=ℂ) (f:=pointB (x i)) ?_; swap; · intro b a ht; rcases a with ⟨⟨a,k⟩,c⟩; rcases b with ⟨⟨b,j⟩,d⟩; simpa [pointB] using! ht -- fix
    apply D_in; rw [← show edge (Q i) (Vane q A i (y i)) (D ((credit q B*textA q l) i)) = _ from cohab q x y _ A i]; change _=D (meets q y x A B i • (textA q l i)+credit q B i* _); rw [map_add,map_smul,map_mul (_), ← show edge _ _ (D (textA q l i))= _ from cohab q x y (textA q l) A i]; change edge _ _ (D (credit q B i * _))=_; rw [map_mul, Derivation.leibniz,show D (credit q B i)=_ from gen q i (x i) B, link]; simp only [smul_eq_mul]; rw [mul_comm _ (MvPolynomial.C _),MvPolynomial.C_mul']; unfold meets; ring
lemma mate_tri : Gτ p (credit q A * a) b= Gτ (cohabit q x y A p) a b+ Gτ p a (cohabit q z y A b):= by
    ext1 i; simp only [gather, Pi.add_apply,Pi.mul_apply, map_mul,gen]; rw [tri_S (A:=dress (x i) (p i)),tri_cross]; rw [cohab,cohab]; apply congr_arg₂ (·+·) <;> exact tri_S ..
end YM.PositionX.Tot
