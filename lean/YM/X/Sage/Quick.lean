import YM.X.Sage.Hawk
/-!
# Aggregate by orientation ticket. Real allocations. Integrated minus vertex in place.Fuel
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r s t R P e:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=>Tet
local notation "o"=>side q k
local notation "ℓ"=> Hair G→₀ℂ
local notation "ε"=>epsilon q k
local notation "Q"=> qu q G k
variable (A:Beacon q G r)(B:Beacon q G s)(C:Beacon q G t)
variable (X Y Z:Fielding.Walk)(p v:Tet)(a:G.ColorIndex)
local notation "A₀"=>veil (X k) k A.seed
local notation "B₀"=>veil (Y k) k B.seed
local notation "C₀"=>veil (Z k) k C.seed
local notation "δ"=> edge Q
local notation "K"=> Weave q
def flock : Weave q:= ∑ a:U,∑ p:T,∑ i:T, Wheel q X i r p * Lapiz B (A.shade i a) X Y Z p a C (t:=-1)
lemma flown (x:Site (side q k)):
  skirt q k (-1) (lift x) p a ((δ (psiF q k (lift x) (-1) p a)) A₀) B₀ C₀ = ∑ i:T,Wheel q X i r p k x * Lapiz (t:=-1) B (A.shade i a) X Y Z p a C k x:= by
     rw [hpick]; simp_rw [skirt_sum,skirt_M, lofty B, smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; rw [wrap_lift]; rfl -- lofty B order check
abbrev Settlement (X Y Z:Fielding.Walk)(A: Beacon q G r)(B: Beacon q G s)(C: Beacon q G t):ℕ→ℂ:= crow q (flock A B C X Y Z)
lemma inlet : levy q X Y Z A.seed B.seed C.seed (tollV₁ q G) = Settlement X Y Z A B C+ Settlement Y Z X B C A+ Settlement Z X Y C A B:= by
    unfold levy Tot.relevant Settlement; rw [← crowd_plus, ← crowd_plus]; apply congr_arg; ext1 k; ext1 z; change school (qu q G k) (veil (X k) k _) (veil (Y k) k _) (veil (Z k) k _) (veil (lift z) k (tollV₁ q G)) = _; rw [vista]; unfold highA; simp_rw [map_sum,map_mul, veil_μ, school_corn, upperFilm]; -- confirm
    simp_rw [flown,flock]; simp only [Finset.sum_apply, Pi.mul_apply,Pi.add_apply, Finset.sum_add_distrib]
-- Aggregate opacity.W.CostF readAt.Linear space
local notation "F₀"=> (fades ℂ)
def RoomT (q:ℕ+)(s t:ℝ)(Y Z: Fielding.Walk): Submodule ℂ (Weave q):= Submodule.span ℂ {p|∃ (i j:Axis) (u v:T) (f:ℕ→ℂ), Released f ∧ p=(View q Y s u i*View q Z t v j)*ensign q f}
variable (χ:Floor R)(h:Geom q e X Y Z) (hr:R<e)(hq:1<q.val)
include h hr χ hq
local notation "ρ"=> RoomT q s t Y Z
lemma pose_a (F:Foam G)(hf:Apt q e F)(i j:Axis)(b:G.ColorIndex): staple B F X Y Z i j a b C∈ ρ:= by
    unfold staple; apply Submodule.sum_mem; intro u _; apply Submodule.sum_mem; intro v _; refine Submodule.subset_span ⟨i,j,u,v,_,?_,rfl⟩; exact g_cost X Y Z _ _ _ h (χ.positive.trans hr) hq hf (B.light _ _) (C.light _ _)
lemma reminiscent : Lapiz (t:=P) B (A.shade v a) X Y Z p a C∈ RoomT q s t Y Z:= by
    unfold Lapiz; refine Submodule.sum_mem _ (fun i hi=>Submodule.smul_mem _ _ ?_); refine Submodule.add_mem _ ?_ ?_; all_goals apply pose_a B <;> (first| assumption| exact illA _ _ (A.light v a) hq (χ.positive.trans hr)| done) -- order check needs arguments.Supply
omit h hr hq χ
lemma read_add (A B:Weave q): readAt q X (A+B)=readAt q X A+readAt q X B:= rfl
lemma read_sc (A:Weave q)(s:ℂ):readAt q X (s • A)=s • readAt q X A:=rfl
lemma read_multi (A:Weave q)(f:ℕ→ℂ): readAt q X (A*ensign q f)=readAt q X A*f:=rfl
local notation "D"=> Wheel q X p (-1) v
include h hr hq χ a
lemma covered (F:Weave q)(he:F∈ RoomT q r s Y Z) : CostF (crow q (D*F)) (if p=v then readAt q X F else 0):= by
    induction he using Submodule.span_induction with
    | mem i hi=>
        obtain ⟨i,j,u,v',f,h₁,rfl⟩:= hi; let A:=View q Y r u i; let B:=View q Z s v' j; let F:=A*B; rw [←mul_assoc D, crowd_time,read_multi]; rw [show (if p=v then readAt q X F*f else 0)=(if p=v then readAt q X F else 0)*f from ?_]; swap; · split_ifs <;> simp
        rw [mul_comm _ f,mul_comm _ f]; exact (collapse_v p v u v' i j X Y Z hq χ a h hr r s).mul h₁ -- orientation
    | zero=>rw [mul_zero, show readAt q X 0=0 from rfl]; rw [show crow q 0=0 from funext (fun i=>by simp [crow])]; split_ifs <;> exact CostF.reflexive
    | add f g _ _ x y=>rw [mul_add,crowd_plus, read_add]; have he:=x.add y; split_ifs at * with H <;> first| exact he | (rw [add_zero] at he; exact he) -- split all
    | smul c f _ y=>rw [mul_smul_comm,crowd_scale,read_sc]; have he:= y.scalar c; split_ifs at * with h<;> first|exact he|(rw [smul_zero] at he; exact he)
omit a
variable (M:Beacon q G (-1))
lemma matched : CostF (Settlement X Y Z M B C) (ripple X Y Z B.seed C.seed M):= by
    unfold Settlement flock; simp_rw [crowd_onto];
    let F(a:U)(p i:T):K := Lapiz (t:=-1) B (M.shade i a) X Y Z p a C; let f(a:U)(p i:T):ℕ→ℂ:= readAt q X (F a p i); rw [show ripple X Y Z B.seed C.seed M=∑ a:U,∑ p:T,∑ i:T, if i=p then f a p i else 0 from ?_]; swap; · simp; rw [Finset.sum_comm]; unfold ripple f F; simp_rw [groundC] --
    refine CostF.fin _ _ _ fun a _=> CostF.fin _ _ _ fun p _=> CostF.fin _ _ _ fun i _=> covered X Y Z i p a χ h hr hq (F a p i) (reminiscent M B C X Y Z p i a χ h hr hq)
end YM.PositionX.Sage
