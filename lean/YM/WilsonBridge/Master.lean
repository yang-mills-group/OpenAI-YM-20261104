import YM.WilsonBridge.Resolution
import YM.MS.Swirl.Plane

/-!
# BV scalar identity at `Endμ` with invariant marks

The BV Laplacian here is the **unsmoothed** one on the *independent* based-gauge
coordinates. It checks equality of the *formal perturbative series* on two gauge
fixings by finite polynomial identities. Series log/exponential and mark product
conventions are precisely the ones used by Swirl. Coupling substitution may also
be done separately.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit MS.Book
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open Function Finset
open scoped BigOperators
variable {V I : Type} {p : Sector V} [Fintype V] [Fintype I]
variable {B : Bonded p I} {F G H Y : T (Raw V ℂ)}
namespace FreeBV
variable (Q : FreeBV B)
local notation "M" => PermV p
local notation "Δ" => B.BV (R:=ℂ)
local infixl:70 " ⋆ " => Actors.core M

def total : Linear (T (Raw V ℂ)) (T (Raw V ℂ)):= pointL ℕ Q.boundary
def crossBV (B:Bonded p I): Angled (T (Raw V ℂ)):= useN.Lift (tokenL B.BV true p)
local notation "‹" X ":" Y "›" => crossBV B X Y
local notation "DΩ" => Q.total

omit [Fintype V] in
lemma product_promote : F ⋆ G = pairW (product p) F G := rfl
omit [Fintype V] in
lemma cross_promote : ‹F:G›=pairW (tokenL B.BV true p) F G:= rfl
omit [Fintype V] in
lemma guard_retrace (h:F∈(M).guard) : Pure p false (retrace F) := by
  intro l hl
  apply PowerSeries.ext; intro n
  rw [rback]
  change _=PowerSeries.coeff n 0; rw [map_zero]; exact (show Pure p false (F n) from h n (Set.mem_univ _)) l hl
omit [Fintype V] in
lemma central (h:F∈(M).guard) (G) : F ⋆ G=G ⋆ F := by
  rw [product_promote, product_promote]
  apply retrace.injective; rw [← product_r, ← product_r]
  exact (guard_retrace h).central _
omit [Fintype V] in
lemma cross_central (h:F∈(M).guard) (hg:G∈(M).guard) : ‹F:G›=‹G:F› := by
  rw [cross_promote,cross_promote]
  apply retrace.injective; rw [← trips, ← trips]
  exact link_commute _ (guard_retrace h) (guard_retrace hg)
omit [Fintype V] in
lemma cross_left (h:F∈(M).guard) (hg:G∈(M).guard) : ‹F ⋆ G:H›= F ⋆ ‹G:H› + G ⋆ ‹F:H› := by
  apply retrace.injective
  simp_rw [cross_promote,product_promote,map_add,← trips, ← product_r,← trips]
  exact B.costs.paired_left (guard_retrace hg) (guard_retrace h)

lemma product_total (h:F∈(M).guard) (G) : DΩ (F ⋆ G)=DΩ F ⋆ G + F ⋆ DΩ G + ‹F:G› := by
  funext i; simp only [Pi.add_apply]
  change Q.boundary (useN.Lift (product p) F G i)=useN.Lift (product p) (pointL ℕ Q.boundary F) G i+useN.Lift (product p) F (pointL ℕ Q.boundary G) i+useN.Lift (tokenL Δ true p) F G i
  simp_rw [SplitP.loan,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  have he : Pure p false (F j.1) := h j.1 (Set.mem_univ _)
  change Q.boundary (product p _ _) = product p (Q.boundary _) _ + product p _ (Q.boundary _) + link Δ true p _ _
  rw [Q.boundary_apply,Q.Q.product_rule he, link_even (b:=true) Δ he, Q.boundary_apply,Q.boundary_apply]
  simp only [cross_false',one_smul,map_add,LinearMap.add_apply]; abel
lemma total_unit : DΩ (M).unit=0 := by
  funext i; change Q.boundary (useN.refineV (coin 1) i)=0; unfold SplitP.refineV; split
  · rw [Q.boundary_apply, Q.Q.on_coin]; simp [Bonded.BV,loop,LinearMap.sum_apply,coin_nod]
  exact map_zero _
omit [Fintype V] in
lemma cross_unit : ‹(M).unit:F›=0 := by
  change useN.Lift (tokenL Δ true p) (useN.refineV (coin 1)) F=0
  rw [SplitP.tile]; funext i; change link Δ true p (coin 1) _=0
  rw [B.by_lap (coin_pure _)]; simp [coin_nod]

variable (h:F ∈ (PermV p).guard)
include h
local notation "E_" => Actors.wages M F
local notation "d" => ((2:ℂ)⁻¹) • ‹F:F›
omit [Fintype V] in
lemma wage_brackets (n:ℕ) : ‹E_ (n+1):G› = ‹F:G› ⋆ E_ n := by
  induction n with
  | zero => simp_rw [nextW (n:=0),firstW,(M).identityR]; norm_num
  | succ n ih =>
    rw [nextW (n:=n+1),map_smul,LinearMap.smul_apply,cross_left h (wage_earn h _), ih,central (wage_earn h _) _]
    rw [← central (wage_earn h n) ‹F:G›,← (M).star_a, nextNF, map_smul,LinearMap.smul_apply,central (wage_earn h (n+1)) ‹F:G›]
    rw [inv_smul_eq_iff₀ (zeroN' (n+1))]; push_cast; module
lemma total_wage1 (n:ℕ) : DΩ (E_ (n+1+1)) = DΩ F ⋆ E_ (n+1) + d ⋆ E_ n := by
  have hz (m:ℕ) : F ⋆ (DΩ F ⋆ E_ m)=(m+1:ℂ) • (DΩ F ⋆ E_ (m+1)) := by
    rw [← (M).star_a,central h _, (M).star_a,nextNF,map_smul]
  have he (m:ℕ) : F ⋆ (d ⋆ E_ m)=(m+1:ℂ) • (d ⋆ E_ (m+1)) := by
    rw [← (M).star_a,central h _, (M).star_a,nextNF,map_smul]
  have hu (m:ℕ) : ‹F:E_ (m+1)›= (2:ℂ) • (d ⋆ E_ m) := by
    rw [cross_central h (wage_earn h _),wage_brackets h,map_smul,LinearMap.smul_apply,smul_inv_smul₀ (by norm_num : (2:ℂ)≠0)]
  induction n with
  | zero =>
    rw [nextW (n:=0+1),map_smul, product_total Q h, hu 0]
    have ht : DΩ (E_ (0+1))=DΩ F ⋆ E_ 0 := by rw [nextW (n:=0), firstW, (M).identityR, (M).identityR]; simp
    rw [ht,hz,inv_smul_eq_iff₀ (zeroN' (0+1))]; norm_num; module
  | succ n ih =>
    rw [nextW (n:=n+2),map_smul,product_total Q h,hu (n+1),ih,map_add,hz,he,inv_smul_eq_iff₀ (zeroN' (n+1+1))]; push_cast; module

variable (hv : F 0=0)
include hv
lemma annihilates (hm : DΩ F+d=0) : DΩ (exp0 p F)=0 := by
  have hw (n:ℕ) : DΩ ((M).cheers F (n+1)) = -(d ⋆ E_ n) := by
    have hm : DΩ F= -d:= eq_neg_of_add_eq_zero_left hm
    induction n with
    | zero =>
      unfold cheers; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [show wages M F 0= _ from firstW, nextW (n:=0),firstW,(M).identityR,(M).identityR]; simpa [map_add,Q.total_unit] using hm
    | succ n ih =>
      rw [show (M).cheers F (n+1+1)= (M).cheers F (n+1)+ E_ (n+1+1) from Finset.sum_range_succ ..,map_add, ih, Q.total_wage1 h n, hm,map_neg,LinearMap.neg_apply]; abel
  funext i; change Q.boundary _=0
  rw [show exp0 p F i = (M).cheers F (i+1) i from (Actors.overbook (actor p) useN F hv (show useN.grade i ≤ i+1 from Nat.le_add_right ..)).symm]
  have he : Happy useN d:= by
    change ((2:ℂ)⁻¹) • (useN.Lift (tokenL B.BV true p) F F 0)=0
    rw [useN.loan,show useN.pieces 0={((0:ℕ),(0:ℕ))} from useN.home, Finset.sum_singleton]
    simp [hv]
  change DΩ _ i= _
  rw [hw i,Pi.neg_apply,show (d ⋆ E_ i) i=0 from Dynamics.floor_X ( «M» :=actor p) useN hv i i le_rfl he,neg_zero]

omit h [Fintype V] in
private lemma pin (j:ℕ) {n} (hj:j ≤ n) : (M).cheers F n j= exp0 p F j:= Actors.overbook (actor p) useN F hv (show useN.grade j ≤ n from hj) -- h unused
omit [Fintype V] in
lemma exp_brackets : ‹exp0 p F:G›= ‹F:G› ⋆ exp0 p F := by
  have H (n:ℕ) : ‹(M).cheers F (n+1): G›= ‹F:G› ⋆ (M).cheers F n:= by
    unfold cheers; rw [map_sum,LinearMap.sum_apply,map_sum,Finset.sum_range_succ']; simp_rw [firstW,wage_brackets h]; change _+crossBV B (PermV p).unit G=_; rw [cross_unit,add_zero]
  funext i
  change useN.Lift (tokenL Δ true p) _ _ _=useN.Lift (product p) _ _ _
  apply Eq.trans _ ((congr_fun (H i) i).trans ?_)
  · change useN.Lift (tokenL Δ true p) _ G _= useN.Lift (tokenL Δ true p) _ G _; simp_rw [loan]; refine Finset.sum_congr rfl fun j hj=>?_
    rw [pin (p:=p) hv j.1 (by have ht:= mem_antidiagonal.mp hj; omega)]
  · change useN.Lift (product p) ‹F:G› _ _ = useN.Lift (product p) ‹F:G› _ _; simp_rw [loan]; refine Finset.sum_congr rfl fun j hj=>?_
    rw [pin (p:=p) hv j.2 (by have ht:= mem_antidiagonal.mp hj; omega)]

lemma closed_series (hm:DΩ F+d=0) (he:DΩ G+ ‹F:G›=0) : DΩ (exp0 p F ⋆ G)=0:= by
  have hh : exp0 p F ∈ (M).guard:= Cinch.totalZ (P:=useN) h
  rw [Q.product_total hh, Q.annihilates h hv hm,map_zero,LinearMap.zero_apply,zero_add,
    exp_brackets h hv,← central hh _,← map_add,he,map_zero]
end FreeBV
end YM.WilsonBridge
