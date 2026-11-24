import YM.MS.Swirl.Resolute
import YM.MS.Echo.Target
/-!
# Recover connected correlators from moments (fixed torus and eventual by coefficients)
No partition-of-partition sum; Euler.Clock.Θ. All statement on ALL s. Extensionality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset MeasureTheory Real
open Koszul Plane Orbit Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl
open scoped Topology ContDiff Interval
variable {P I E J W:Type}{l:Filter P}[LinearOrder W]
    [AddCommGroup E][Module ℂ E](S:SplitP I){X Y:P→I→T E}{x y:I→T E}
variable {M:Actors E}
set_option quotPrecheck false
local notation "T'"=> M.stack useN
local notation "C" => Cheer ( T' ) S
local infix:70 " ⋆ "=> Actors.core T'
local notation "ι"=> S.origin
open Swirl
-- apart.x cut universal except (x,∅), not relying on powers vanish if ∅.
def rest (x:I): Finset (I× I):= open Classical in (S.pieces x).erase (x,S.origin)
lemma keepL {i a b:I} (h:(a,b)∈rest S i): S.grade a<S.grade i ∧(a,b)∈ S.pieces i := by
    classical
    obtain hp:= Finset.mem_erase.mp h; obtain hu:= S.pays hp.2; refine ⟨?_,hp.2⟩; by_contra hz; obtain he : b=ι:= ( S.zeroC _ ).mp (by omega); subst b; obtain he:= ( S.quiet i a ).mp ( S.sym.mp hp.2 ); exact hp.1 (by rw [he])
-- x T
abbrev flight (M:Actors E)(x:I→T E): Prop:= x∈allIndex ( (M.stack useN).guard ) I
lemma handle (h:Happy S x)(hp: flight M x)(i:I): ( S.grade i:ℂ ) • C x i=( S.grade i:ℂ ) • x i+∑ v∈ rest S i,( ( S.grade v.1:ℂ ) • x v.1 ) ⋆ ( C x v.2 ):= by
    classical
    obtain hX:= Cinch.idea ( turn_clock S T' ) hp h; rw [ ← cloak S ( C x ) i,hX ]; change S.Lift (T').core _ _ _=_; rw [S.loan, ← Finset.add_sum_erase (a:=(i,ι)) (s:=S.pieces i) _ ( S.sym.mp (( S.quiet .. ).mpr rfl)) ]; congr 1; · rw [Stencil.simple_E ( T' ) x S h,( T' ).identityR ]; rfl
-- weak by coefficient
variable (M)
lemma peaks (h:∀ i,Happy S ( X i )) (hx:∀ i,flight M ( X i )) (hy:∀ i,Happy S ( Y i ))(hp:∀ i, flight M ( Y i ))(hv:∀ i n,∀ᶠ k in l, C ( X k ) i n=C ( Y k ) i n): ∀ i n,∀ᶠ k in l,X k i n=Y k i n := by
    intro i n; induction he:S.grade i using Nat.strong_induction_on generalizing i n with
    | h v ih=>
       by_cases hm:v=0; · rw [( S.zeroC _ ).mp ( he.trans hm ) ]; exact Eventually.of_forall fun k=> congr_fun ( ( h k ).trans ( hy k ).symm ) n
       have hb (k i n): C ( X k ) i n= C ( X k ) i n:= rfl; let Φ(i:I)(x:I→T E):= (S.grade i:ℂ) • x i; let z(u:I× I)(x:I→T E): E:= (Φ u.1 x ⋆ C x u.2) n; let c:= S.grade i; have hz : (c:ℂ)≠0:= by unfold c; exact_mod_cast ( ne_of_eq_of_ne he hm ) -- name
       have hP(x:I→ T E)(he: flight M x)(hh: Happy S x): (c:ℂ) • C x i n=(c:ℂ) • x i n+∑ v∈ rest S i,z v x:= by obtain hm:= congr_fun (handle S hh he i) n; rw [Pi.add_apply, Finset.sum_apply] at hm; exact hm
       have hr v (ht:v∈rest S i): ∀ᶠ k in l,z v ( X k )= z v ( Y k ):= by
           obtain ht:= keepL S ht; let F(k:ℕ):=antidiagonal k; have he u (hu:u∈ F n): ∀ᶠ k in l,M.core ( Φ v.1 ( X k ) u.1 ) ( C ( X k ) v.2 u.2 ) =M.core ( Φ v.1 ( Y k ) u.1 ) ( C ( Y k ) v.2 u.2 ):= by
              filter_upwards [ ih _ ( i:=v.1 ) (Nat.lt_of_lt_of_le ht.1 (le_of_eq he)) u.1 rfl, hv v.2 u.2 ] with k hx hm; unfold Φ; rw [ Pi.smul_apply, Pi.smul_apply, hm,hx ] -- ih argument order
           filter_upwards [ (eventually_all_finset _).mpr he ] with p hp; unfold z; exact Finset.sum_congr rfl fun j hj=>hp j hj
       filter_upwards [ (eventually_all_finset _).mpr hr,hv i n ] with k hk hh; apply (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr hz)).mp; exact add_right_cancel ( (hP ( X k ) ( hx k ) ( h k )).symm.trans ( by rw [ hh,hP _ (hp k) ( hy k), Finset.sum_congr rfl hk ] ) ) -- sum congr hk
-- resulting
end YM.MS.Tide
