import YM.MS.Swirl.Dry
/-!
# Logarithm. Arbitrary grade-cuts.Caveat Only applied to unit-at-origin. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve Actors Engine Dynamics Stencil Swirl
open scoped Topology ContDiff Interval
variable {I E F : Type}[ AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F]
namespace Log
variable (M:Actors E)(P:SplitP I) {x:I}
set_option quotPrecheck false
local notation "g"=> P.grade
local notation "ι"=> P.origin
local infix:70 " ⋆ "=> M.core
local infix:69 " ⋄ "=> (M.stack P).core
def restS (i:I): Finset (I×I):= open Classical in (P.pieces i).erase (i,P.origin)
lemma keep {p:I×I} (h:p∈restS P x): g p.1< g x:= by
   classical
   obtain ⟨hp,hv⟩:= Finset.mem_erase.mp h; obtain he:=P.pays hv; by_contra hr; obtain hy:p.2=ι:=(P.zeroC _).mp (by omega); apply hp; obtain hq:= P.sym.mp hv; rw [hy] at hq; exact Prod.ext ( ( P.quiet x p.1 ).mp hq|>.symm ) hy
variable (y:I→E)
-- unit not assumed except solve
abbrev α (i:I):ℂ:= P.grade i
def issue (e:I→ E) (i:I): E:= clock P E y i- ∑ j∈ restS P i, ( α P j.1 • e j.1 ) ⋆ y j.2
def logV : ℕ→ I→ E| 0=>0| n+1=> fun i:I=> ( α P i )⁻¹ • issue M P y (logV n) i
abbrev Meter (i:I): E:= logV M P y ( P.grade i ) i
lemma corner (t:I→E)(eI:y ι=M.unit) (i:I): (α P i) • t i=issue M P y t i ↔ clock P E y i= (P.Lift M.core ( clock P E t ) y i ):= by
    classical
    rw [ P.loan, ← Finset.add_sum_erase (s:= P.pieces i) (a:=(i,ι)) _ ( P.sym.mp (( P.quiet i i ).mpr rfl) ) ]; dsimp only; rw [eI, M.identityR ]; simp_rw [ issue, cloak, α ]; exact eq_sub_iff_add_eq.trans eq_comm -- cloak sum erase? rest
lemma unit (n:ℕ)(v:I)(h:g v=0): logV M P y n v=0:= by cases n; rfl; simp [ logV,α,h ]
lemma sta (w:I)(n k:ℕ)(hx:g w≤n)(hk:g w≤k): logV M P y n w=logV M P y k w := by
    induction n generalizing w k with
    | zero=> rw [unit M P y 0 w (by omega), unit M P y k w (by omega) ]
    | succ n ih=>
       rcases k with _|k; rw [unit M P y _ w ( by omega ),unit M P y _ w (by omega)]; simp only [ logV ]; refine congr_arg (( α P w )⁻¹ • · ) (congr_arg (clock P E y w - ·) ?_); exact Finset.sum_congr rfl (fun i hi=> by rw [ ih i.1 k (by obtain h:= keep P hi; omega ) (by obtain h:= keep P hi; omega ) ])
lemma thenP (n:ℕ)(x:I)(hv:g x≤n): Meter M P y x=logV M P y n x:= sta M P y x (g x) n le_rfl hv
lemma spawn (x:I): Meter M P y x=( α P x )⁻¹ • issue M P y (Meter M P y) x := by
   nth_rw 1 [thenP M P y (g x+1) x (by omega), logV ]; refine congr_arg (( α P x )⁻¹ • · ) (congr_arg (clock P E y x- · ) (Finset.sum_congr rfl (fun i hi=>?_))); rw [ ← thenP M P y (g x) i.1 ( keep P hi|>.le ) ] -- lambda issue matching
lemma happy : Happy P (Meter M P y):=unit M P y (g ι) _ (( P.zeroC _ ).mpr rfl)
lemma MeterIN (V:Submodule ℂ E)(hu:∀ x∈ V,∀ w∈V,( x ⋆ w )∈V) (hv:∀ i,y i∈V)(u:I): Meter M P y u∈ V := by
    unfold Meter; generalize g u=n; induction n generalizing u with| zero=> exact V.zero_mem| succ n ih=> exact V.smul_mem _ ( V.sub_mem ( V.smul_mem (α P _) (hv _) ) ( V.sum_mem fun a _=> hu _ ( V.smul_mem (α P _) (ih _) ) _ ( hv _ ) ) ) -- generalize P notation?
lemma motionL (he:y ι=M.unit)(i:I): clock P E y i=(P.Lift M.core (clock P E ( Meter M P y )) y i):= by
    have hh := turn_clock P M; obtain h|h:=eq_or_ne i ι; · subst i; rw [P.loan,P.home]; simp only [Finset.sum_singleton, cloak, α,( P.zeroC _ ).mpr rfl,Nat.cast_zero,zero_smul,map_zero,LinearMap.zero_apply]
    apply (corner M P y _ he i).mp; nth_rw 1 [spawn M P y]; apply smul_inv_smul₀; unfold α; exact_mod_cast (show g i ≠ 0 from fun t=> h ( ( P.zeroC _ ).mp t ))
lemma solve (he:y ι=M.unit)(hp:∀ i,y i∈ M.guard): Cheer M P (Meter M P y)= y:= by
    have hz : Meter M P y∈ allIndex M.guard I:= (universe0 _).mpr ( MeterIN M P y _ M.close hp ); apply tick_agree P M ( tick0 P ( Meter M P y ) ); rw [ simple_E M _ _ (happy M P y), he ]; exact ( turn_clock P M ).idea hz (happy M P y); exact funext (motionL M P y he)
lemma recheck (t:I→E)(hp: t∈ allIndex M.guard I)(hT: Happy P t): Meter M P ( Cheer M P t )= t:= by
    funext i; let Z(i:I):= Cheer M P t i; induction hi:g i using Nat.strong_induction_on generalizing i with
    | h k ih=>
       by_cases h:k=0; · rw [(P.zeroC _).mp ( hi.trans h )]; exact ( happy M P ( Cheer M P t ) ).trans ( show t ι=0 from hT ).symm -- Happy not structure Eq fn
       obtain hS:(α P i)≠0:= by unfold α; exact_mod_cast ( ne_of_eq_of_ne hi h );
       apply (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr hS)).mp; have hv(i:I): clock P E Z i= ( P.Lift M.core ( clock P E t ) Z i ):= congr_fun ( ( turn_clock P M ).idea hp hT ) i
       change _ • _= _ • _; rw [ ( corner M P Z t ( simple_E M _ _ hT ) i ).mpr (hv i) ]; nth_rw 1 [ spawn M P ]; rw [ smul_inv_smul₀ hS ]; refine congr_arg ( clock P E Z i- · ) ( Finset.sum_congr rfl fun j hj=> ?_ ); rw [ ih _ ( j.1 |> g |> (fun _=>?_)) j.1 rfl ]; -- argument patch
       exact hi ▸ keep P hj
end Log
end YM.MS.Puff
