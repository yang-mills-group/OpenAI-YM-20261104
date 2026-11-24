import YM.X.Gravity.Braid
import YM.X.Gravity.Tunic
import YM.X.Bare.Gains
/-!
# Purchase canonical CT in physical free-label submodule. With testing goals later, use unscaled CT here. Not proposing finite-regulator choice N(t) ∗yet∗. Prices to existing lower stencil sector.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark Bare
open Stems hiding X
open Pert.RawLabels
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "Ψ"=> Book G
local notation "e"=>epsilon q
variable {F:Labels.Frames G}(s:Shop F)(P:Word G)(φ:Floor R)
local notation "D"=>P.d
local notation "E"=> Pert.Position.E F
lemma solid (F:Labels.Frames G)(f:Shop F)(P:Word G)(φ:Floor R)(q:ℕ+)(k:ℕ):∃ x:Pert.Position.E F P.d,coreP f P.d x=watch G P.d (exposed q P φ k):= by
    apply (LinearMap.mem_range).mp; rw [purchased]; exact atmospheric ..
include q in
def billet (k:ℕ): E P.d:= (solid F s P φ q k).choose -- include q manually
lemma sold : coreP s P.d (billet (q:=q) s P φ k)=watch G P.d (exposed q P φ k):=(solid ..).choose_spec
lemma fixed_billet : (fun k=>(↑(e k):ℂ) • billet (q:=q) s P φ k)=(fun k=> (coreP s P.d).leftInverse (watch G P.d ( e k • exposed q P φ k))):= by
    funext k; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_smul,←sold (q:=q) s P φ, LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (core_in s))]; rfl
include hq
lemma tend_billet : (fun k=>(↑(e k):ℂ) • billet (q:=q) s P φ k)∈ Badge (Pert.Position.E F P.d) (fun p=>p∈ fades ℂ) ⊤:= by rw [fixed_billet]; exact moved ((coreP s P.d).leftInverse.comp (watch G P.d)) (fun _ _=> Submodule.mem_top) (price_shrink hq P φ)
omit hq
section
variable (j:ℕ)
def matchP (s: Shop F)(q:ℕ+)(j d:ℕ) : Pert.Position.E F d→ₗ[ℂ] Curly G := milk (flow G (side q j)) ∘ₗ raw s d 0 ∘ₗ (physicalLabel F d)
def matchSelf (s: Shop F)(d:ℕ) : Pert.Position.E F d →ₗ[ℂ] Curly G:= Bare.self s d ∘ₗ (physicalLabel F d)
lemma matchS (x:Pert.Position.E F d): bloom d (matchSelf s d x)= coreP s d x:= rfl
include hq in
lemma portion {d:ℕ}(x:Pert.Position.E F d): (fun i=> matchP s q i d x - matchSelf s d x)∈ Badge (Curly G) (Vanished q) (CakeH G):= by
   let f:=physicalLabel F d; let p:= f x; let M k:=flow G (side q k); change (fun i=> milk (M i) (raw s d 0 p)-self s d p)∈_;
   let B:= (F.level d).basis; let I:= (F.level d).Index; let t(i:I):= B.coord i p; let V(i:I)(k):= milk (M k) (raw s d 0 (B i))-self s d (B i)
   have hp(k): milk (M k) (raw s d 0 p)-self s d p= (∑ i:I,t i • V i) k := by
       conv_lhs => rw [← B.sum_repr p]
       simp only [V, map_sum,map_smul, ← Finset.sum_sub_distrib,Finset.sum_apply,Pi.smul_apply,smul_sub]; rfl -- conv rw may fail 
   rw [show (fun i=>_) =_ from funext hp]; apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; unfold V B; simp_rw [raw_name,self_name]; exact self_ration hq (useWord s i)
end
end YM.PositionX.Gravity
