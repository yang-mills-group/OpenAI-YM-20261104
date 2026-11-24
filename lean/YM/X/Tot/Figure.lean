import YM.X.Tot.Share
/-!
# current reading along true lattice PT. `ProbeX` uses curvature *before position renorm*, at non-spin-provisional away. Step circulation mild. budget kernel tangent.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}
variable (S:Shop F)(q:ℕ+)(χ:Floor R)
local notation "μ"=> flow G n
local notation "N"=> side q k
local notation "Q"=> qu q G
local notation "ε"=>epsilon q k
variable (x y z:Fielding.Walk)(A B C:Foam G)
variable (X:Fin 3→Fielding.Walk) (o:Site (side q k)) (v:Fin 3→ Pert.Position.E F d)
abbrev handV {F:Labels.Frames G} (d:ℕ) (v:Fin 3→Pert.Position.E F d):=physicalLabel F d ∘ v
abbrev pV (S:Shop F)(q:ℕ+)(d:ℕ)(v:Fin 3→ Pert.Position.E F d) : Fin 3→ Foam G:= stance S q d ∘ handV d v
abbrev pV₁ (S:Shop F)(q:ℕ+)(χ:Floor R)(d:ℕ)(v:Fin 3→ Pert.Position.E F d) : Fin 3→ Foam G:= highs q χ S d ∘ handV d v
local notation "κ"=> Hinge.shock
lemma triple_fate (q:Symmetric V)(p r s:poly V): κ q (p*(r*s))= tri q (milk q p) (milk q r) (milk q s):= by rw [tri,market,minus,minus,minus,pure,one_mul,mul_assoc]
local notation "Z"=> handV d v
local notation "P"=> pV S q d v
local notation "T"=> pV₁ S q χ d v
local notation "P₀"=> held S ε⁻¹ d 0
lemma stances (i:Fin 3): milk (Q k) (dress (X i k) (P₀ (Z i)))= Lift (X i) (P i) k:= by rw [milked]; unfold Lift; rw [show P i = _ from rfl, pV, comp_apply, stanza_val] -- tidy
lemma nook (GX:poly (Jam (side q k) G)) : let y:= postal X o k; hours S y ε GX d (handV d v)= κ sale (GX * hairAt o ((dress (X 0 k) (P₀ (handV d v 0)))*(dress (X 1 k) (P₀ (handV d v 1))* dress (X 2 k) (P₀ (handV d v 2))))) := by
    intro y; rw [hours,chapter_val,Fin.prod_univ_succ,Fin.prod_univ_two]; apply congr_arg (κ sale); apply congr_arg; simp_rw [sales,LinearMap.comp_apply,map_mul (hairAt o),tint]; rfl -- Z conflicts
lemma initial_est : partM S N ε (postal X o k) d 0 v = gather q (X 0) (X 1) (X 2) (P 0) (P 1) (P 2) k:= by rw [coins_view,nook,one_mul, ← Fund.loc,triple_fate,stances,stances,stances];rfl
-- Upper slots. unpack finite three phi
variable (L:Fin m→Site n)(t:ℝ) (p:Fin m→ Label G d) (i:Fin m) (f:Module.End ℂ (Label G d))
lemma pass_atom : hours S L t 1 d (Function.update p i (f (p i)))= chapters (Function.update (fun i=> sales (d:=d) S 0 t (L i)) i (sales S 0 t (L i) ∘ₗ f)) 1 p:= by
    rw [hours, chapter_val,chapter_val]; congr 2; apply Finset.prod_congr rfl; intro j _; by_cases h:j=i <;> first | (subst j; rw [Function.update_self,Function.update_self]; rfl) | rw [Function.update_of_ne h, Function.update_of_ne h]
lemma combine_atom (p:Fin m→ Label G d)(L:Fin m→ Label G d→ₗ[ℂ] poly (Jam n G))(i:Fin m)(M r: Label G d→ₗ[ℂ] poly (Jam n G)):
     chapters (Function.update L i M) 1 p-chapters (Function.update L i r) 1 p= chapters (Function.update L i (M-r)) 1 p:= by simp_rw [chapter_insert,LinearMap.sub_apply,sub_mul,map_sub]
-- shape normalization w.r.t κ V etc
lemma first_sum : let a:= postal X o k; let g:=handV d v; let θ(i: Fin 3):=hairAt (a i); probeX q S (Pulse.away (k:=k) (q:=q) S χ d) k a v = (∑ i:Fin 3, chapters (Function.update (fun i=> sales (d:=d) S 0 ε (a i)) i ((θ i).toLinearMap ∘ₗ splurge q χ d S k)) 1 g) - hours S a ε (gas G N) d g:= by
    intro a g θ; unfold probeX; rw [MultilinearMap.sub_apply, spend_reply,bill₁_view S _,pass_view]; set b:= physicalLabel F d ∘ₗ (advance (k:=k) (q:=q) S χ d) with hb
    change first_b S _ _ _ g - ∑ i:Fin 3,hours S _ _ 1 d (Function.update g i (b (g i)))= _; unfold first_b; rw [MultilinearMap.sub_apply,MultilinearMap.sum_apply,sub_right_comm,← Finset.sum_sub_distrib];
    apply congr_arg (·- _); refine Finset.sum_congr rfl fun i _=> ?_; rw [pass_atom,combine_atom]; apply congr_arg (fun W=> chapters (Function.update (fun i=> sales (d:=d) S 0 ε (a i)) i W) 1 g); ext1; ext v; rw [splurge]; simp only [←hb,LinearMap.comp_apply,LinearMap.sub_apply,sales,AlgHom.toLinearMap_apply,map_sub];rfl
-- ∆ evaluation with ∑ root. use Sym orbit and stemT.
def liftedA (x:Cover) (n:Side)(A:Curly G):= dress x (milk (flow G n) A)
lemma root3 (f:Fin 3→Curly G) : (κ sale) (∏ i:Fin 3,hairAt (postal X o k i) (f i))= tri (Q k) (liftedA (X 0 k) N (f 0)) (liftedA (X 1 k) N (f 1)) (liftedA (X 2 k) N (f 2)):= by unfold postal Fund.stock liftedA; simp only [← tint, ← Fund.milked]; rw [Fin.prod_univ_succ,Fin.prod_univ_two, ← map_mul (hairAt o), ← map_mul (hairAt o), ← Fund.loc,triple_fate]; rfl -- numeral succ
lemma patchA (i:Fin 3): let y:= postal X o k; let f:=Function.update (P₀ ∘ Z) i (splurge q χ d S k (Z i));
     chapters (Function.update (fun t=> sales (d:=d) S 0 ε (y t)) i ((hairAt (y i)).toLinearMap ∘ₗ splurge q χ d S k)) 1 Z= (κ sale) (∏ i:Fin 3,hairAt (postal X o k i) (f i)):= by intro y f;rw [chapter_val,one_mul]; apply congr_arg; apply Finset.prod_congr rfl; intro j _; unfold f; by_cases h:j=i<;> first|(subst j; rw [Function.update_self,Function.update_self];rfl)|(rw [Function.update_of_ne h, Function.update_of_ne h]; rfl)
end YM.PositionX.Tot
