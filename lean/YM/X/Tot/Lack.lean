import YM.X.Tot.Cistern
/-!
# lack of enough seats at Ψ if pair apertures needed. Handles all reference capacities. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {q:ℕ+} {d k m:ℕ} {V I:Type*} {r:ℝ}
local notation "F₀"=> (fades ℂ)
def Dry (q:ℕ+)(G:Gauge):= Submodule.span ℂ {p:Foam G| ∃ (f:ℕ→ℂ)(P:Foam G), f∈ fades ℂ∧ P∈ Ready q (Reed.Horizontal G) ∧ p=f • P}
variable (x y z:Fielding.Walk){p a b: Foam G} (A:Marks G)(T:Set (Marks G)) (B C: List (Marks G))
local notation "U"=> (Reed.Horizontal G)
local notation "Gτ" => gather q x y z
local notation "xτ"=> textA q
local notation "D"=> Dry q G
abbrev Lined (q:ℕ+)(A B:Set (Marks G))(x y:Fielding.Walk) := ∀a∈A,∀b∈B, meets q x y a b∈ F₀
lemma page_all (l:List (Marks G)) : textA q l∈ Ready q U:= page_spec _ _ _ (fun _ _=> Set.mem_univ _) (Set.mem_univ _)
lemma Dry.join (v:ℕ→ℂ)(h:v∈F₀)(hp:p∈Ready q U) : v • p∈ Dry q G:= Submodule.subset_span ⟨_,_,h,hp,rfl⟩
lemma Dry.step (h:p∈Dry q G): credit q A * p∈Dry q G:= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨f,t,v,h,rfl⟩:=hi; rw [foamX];exact Dry.join _ v (choose_p q _ A (Set.mem_univ _) _ _ (fun _ _=> Set.mem_univ _) t h)
    | zero=> simp
    | add a b _ _ x y=> rw [mul_add];exact Submodule.add_mem _ x y
    | smul a m _ h=>rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
lemma cohabit_dry (h:∀a∈B, meets q x y A a ∈ fades ℂ): cohabit q y x A (textA q B)∈ D:= by
    induction B with
    | nil=> rw [Tot.empty,show cohabit _ _ _ _ 1=0 from funext fun i=> Derivation.map_one_eq_zero _]; exact Submodule.zero_mem _
    | cons a l IH=> rw [mate_cons]; exact Submodule.add_mem _ (Dry.join _ (h _ (by simp)) (page_all _)) (Dry.step a (IH (fun i hi=> h i (by simp [hi]))))
variable (h:Geom q r x y z)(hr:0<r)(hq:1<q.val)
include hr hq
include h
lemma dry_tip (hp:Apt q r p) (ha:a∈Ready q U) (hb:b∈ Dry q G): gather q x y z p a b∈ fades ℂ:= by
    induction hb using Submodule.span_induction with
    | mem i hi=> obtain ⟨f,t,u,v,rfl⟩:=hi; rw [← gather_sym q z, gather_up,gather_sym q z,mul_comm]; exact usual_fading _ f (g_cost x y z _ _ _ h hr hq hp ha v) u
    | zero=> rw [← gather_sym q z, show gather q z x y 0 p a=0 from funext fun i=>by simp [gather]]; exact Submodule.zero_mem _
    | add t v _ _ x' hx=> rw [← gather_sym q z, gather_add]; rw [← gather_sym q z] at x' hx; exact Submodule.add_mem _ x' hx
    | smul t v _ h=> rw [←gather_sym q z,show t • v=(fun _:ℕ=>t) • v from rfl, gather_up]; rw [← gather_sym q z] at h;exact Submodule.smul_mem _ t h
omit h
lemma sup_tide (h:Clear q r x y): Tide q r (supF q (x-y) A):= by obtain ⟨a,b,ht,hp,hb⟩:=h; exact from_tide hq hr.le hb (plot.sub ht hp) A.x A.order A.sector
include h
abbrev heightY (q:Foam G)(d:ℕ):= ∀ i:ℕ,duty (q i) d
omit hr hq h in
lemma Page.duty' {T:Set ℕ}(hp:p∈Page q T (Set.univ (α:=Marks G))) (ht:∀ m∈ T,m≤d):heightY p d:= by -- fix
    induction hp using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,f,h,hf,h',rfl⟩:=hi; intro i; refine duty.scalar (f i) (duty.more (leafy.mp (echelon q l i) ▸ Heat.Top.cut_bound _ _) (ht _ h'))
    | zero=> intro;exact duty.zero
    | add a t _ _ x y=>intro i; exact (x i).add (y i)
    | smul a t _ h=> intro i; exact (h i).scalar _
set_option maxHeartbeats 400000 in
lemma Lack (hp:Apt q r p) (hh:heightY p d)(hx:d<B.length+C.length)(hy:∀ a∈B,∀ b∈C, meets q y z a b∈ F₀): Gτ p (xτ B) (xτ C) ∈ F₀:= by
    generalize hE:B.length+C.length = k at hx; induction k using Nat.strong_induction_on generalizing x y z d p B C with
    | h k ih=>
       have hterm(y z:Fielding.Walk)(h:Geom q r x y z)(B C:List (Marks G))(a:Marks G)(hp:B.length+1+C.length=k)(hy:∀ v∈a::B,∀ c∈C,meets q y z v c∈ F₀): gather q x y z p (xτ (a::B)) (xτ C) ∈ F₀:= by -- collision hp double
          rw [text_cons,mate_tri]; apply Submodule.add_mem; swap; · exact dry_tip _ _ _ h hr hq (by assumption) (page_all B) (cohabit_dry y z a C (hy a (by simp)))
          cases d with
          | zero => rw [show cohabit q x y a p=0 from funext (fun i=>slit_null _ (hh i)), show gather q x y z 0 (xτ B) (xτ C)=0 from funext fun i=> by simp [gather]]; exact Submodule.zero_mem _
          | succ d=>
             have he : Geom q r x y z:= h; have hx' : d < B.length+C.length:= by omega
             have ht := sup_tide y x a hr hq (he.1.sym q x y); exact ih _ (by omega : B.length+C.length<k) x y z (p:=cohabit q x y a p) B C h (Apt.stamp (by assumption : Apt q r p) _ ht) (fun i=> slit_budget _ (hh i)) (fun b hb=> hy b (by simp [hb])) rfl hx'
       cases B with
       | cons a B=>exact hterm y z h B C a hE hy
       | nil=> rcases C with _|⟨c,C⟩; · simp [List.length_nil] at hE; omega
               rw [gather_swap]; exact hterm z y (Geom.swap _ _ _ _ h) C [] c (by simp_all) (by simp)
end YM.PositionX.Tot
