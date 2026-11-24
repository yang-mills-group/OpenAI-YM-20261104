import YM.X.Tot.Room
/-!
# Shape casts with opacity P. Combined with derivative Towers Ple
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ}
local notation "fℕ"=>(atTop:Filter ℕ)
variable (q:ℕ+)(x y z:Fielding.Walk)(χ:Floor R)
local notation "K"=> Billboard G q
local notation "Ω"=> Foam G
variable {T₁ T₂ T₃:Set ℕ}{B₁ B₂ B₃:Set (Marks G)}
variable (A B C': Billboard G q)(X:A∈Slalom q x 0 T₁ B₁)(Y:B∈Slalom q y 0 T₂ B₂)(Z:C'∈Slalom q z 0 T₃ B₃)(P:ChaseR)(hP:Usual P)
variable (h:Geom q r x y z)(hq:1<q.val)(hr:R<r)
local notation "K₁"=> Core q x y z (T₁:=T₁) (T₂:=T₂) (T₃:=T₃) (B₁:=B₁) (B₂:=B₂) (B₃:=B₃)
local notation "D"=> (1-bend q χ x)
local notation "T"=> Page q {3} (Set.univ (α:=Tops G))
include h hq hr χ
omit hr χ in
lemma inner_crew (hr:0<r):K₁ k d m Shelf.crew:= fun a b c t u v=>g_cost x y z a b c h hr hq (illA _ _ t hq hr) u v
include X Y Z hP
lemma page_full {V:Foam G}(hp:V∈Page q {3} (Set.univ (α:=Tops G))) (he: K₁ 1 1 1 P): relevant q A B C' (vertexLift q V)∈P:= by
    induction hp using Submodule.span_induction with
    | mem i hi=>
       obtain ⟨l,t,ht,_,h',rfl⟩:=hi; obtain ⟨a,b,c,h'⟩:= List.length_eq_three.mp (show l.length=3 from h'); rw [viz_p,rv_scale,h']; simp only [text_cons,empty,mul_one]; exact hP _ _ ht (legal_I q x y z χ a b c A B C' X Y Z P hP h hq hr he)
    | zero=> rw [map_zero,relevant_zero]; exact P.zero_mem
    | add a b _ _ t u=> rw [map_add,relevant_v]; exact P.add_mem t u
    | smul a b _ t=> rw [map_smul,rv_const]; exact P.smul_mem _ t
lemma page_maj {V:Foam G}(hp:V∈Page q {3} (Set.univ (α:=Tops G))) (h1:K₁ 3 0 0 P)(h2:K₁ 2 1 0 P)(h3:K₁ 2 0 1 P): mantle q D A B C' (vertexLift q V)∈P:= by
    induction hp using Submodule.span_induction with
    | mem i hi=>
       obtain ⟨l,t,ht,_,h',rfl⟩:=hi; obtain ⟨a,b,c,h'⟩:= List.length_eq_three.mp (show l.length=3 from h'); rw [viz_p,mantle_vert_scale,h']; simp only [text_cons,empty,mul_one]; exact hP _ _ ht (legal_M q x y z χ a b c A B C' X Y Z P hP h hq hr h1 h2 h3)
    | zero=> rw [map_zero,mantle_zero]; exact P.zero_mem
    | add a b _ _ t u=> rw [map_add,mantle_vert_up]; exact P.add_mem t u
    | smul a b _ t=> rw [map_smul,mantle_scale_v]; exact P.smul_mem _ t
omit h hq X Y Z χ hP hr
-- E actions on physical family. useful compact projectors costs SC. Keep λ majority masks at three supports.
abbrev deckQ (q:ℕ+)(χ:Floor R)(x:Fielding.Walk):=1-bend q χ x
def bill (A B C':K)(V: Billboard G q): ℕ→ℂ:= relevant q A B C' V + (mantle q (deckQ q χ x) A B C' V +mantle q (deckQ q χ y) B C' A V + mantle q (deckQ q χ z) C' A B V)
include χ
lemma bill_rotate (V:K) : bill q x y z χ A B C' V= bill q y z x χ B C' A V:= by unfold bill; rw [elected q A]; ring
lemma bill_swap (V:K): bill q x y z χ A B C' V=bill q x z y χ A C' B V:= by unfold bill; rw [elect₁ q A B,maj_swap (B:=B) (A:=A), maj_swap (C':=B) (A:=C'),maj_swap (A:=B) (C':=A)]; ring
local notation "L"=> bill q x y z χ
omit χ
lemma v_addA (V Z:K): relevant q (A+B) C' V Z= relevant q A C' V Z+relevant q B C' V Z:= by
     ext1 i; unfold relevant crow; have he (Q:Symmetric (Hair G))(A B C D' Z:Curly G): school Q (A+B) C D' Z=school Q A C D' Z+school Q B C D' Z:= by
         unfold school; rw [space_X Q (A+B),space_add,space_X Q A,space_X Q B]; unfold majority; rw [madd,tri_plus,tri_plus₁,tri_plus₁]; ring
     simp_rw [Pi.add_apply,he, Finset.sum_add_distrib, mul_add]
lemma v_scaleA (V:K)(c:ℕ→ℂ) : relevant q (ensign q c • A) B C' V=c*relevant q A B C' V:= by
     have he(R:Symmetric (Hair G))(A B C D':Curly G)(a:ℂ): school R (a • A) B C D'=a • school R A B C D':= by unfold school; rw [space_X R (a • A),space_scale,space_X R A]; unfold majority; rw [mscale',tri_scale,tri_scale₁,tri_scale₁]; simp only [smul_sub]
     ext1 i; change volS q i * (∑ z:Site (side q i),school _ (c i • A i z) (B i z) (C' i z) (V i z)) = c i * relevant q A B C' V i; simp_rw [relevant,crow,he,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
include χ
lemma bill_add (U V:K): bill q x y z χ (A+U) B C' V=L A B C' V+L U B C' V:= by unfold bill; rw [v_addA,mantle_add,mantle_add', maj_swap (B:=C') (C':=A+U), mantle_add',maj_swap (C':=C') (B:=A),maj_swap (C':=C') (B:=U)]; ring
lemma bill_sc (U:K)(c:ℕ→ℂ): L (ensign q c • A) B C' U=c*L A B C' U:= by unfold bill; rw [v_scaleA,mantle_scale,mantle_scale', maj_swap (B:=C') (C':=ensign _ _ • A), mantle_scale',maj_swap (C':=C') (B:=A)]; ring
lemma bill_cost (V:Foam G)(hv:V∈ T)(X':A∈ Slalom q x 0 T₁ B₁)(Y':B∈ Slalom q y 0 T₂ B₂)(Z':C'∈ Slalom q z 0 T₃ B₃)(h:Geom q r x y z)(hq:1<q.val)(hr:R<r): Released (L A B C' (vertexLift q V)):= by
    have hr' := χ.positive.trans hr; let g:=h.circles q x y z; refine Released.add ?_ (Released.add (Released.add ?_ ?_) ?_)
    · exact page_full q x y z χ A B C' X' Y' Z' Shelf.crew usual_crew h hq hr hv (inner_crew q x y z h hq hr')
    · apply (page_maj q x y z χ A B C' X' Y' Z' Shelf.crew usual_crew h hq hr hv) <;> apply inner_crew q x y z h hq hr'
    · apply (page_maj q y z x χ B C' A Y' Z' X' Shelf.crew usual_crew g hq hr hv) <;> apply inner_crew _ _ _ _ g hq hr'
    · apply (page_maj q z x y χ C' A B Z' X' Y' Shelf.crew usual_crew (g.circles q ..) hq hr hv) <;> apply inner_crew _ _ _ _ (g.circles q ..) hq hr'
end YM.PositionX.Tot
