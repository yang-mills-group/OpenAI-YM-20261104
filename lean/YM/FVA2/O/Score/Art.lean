import YM.FVA2.O.Score.Band
/-!
# Installation of all the graded physical basis correlation arrays

`install`: from a given family of the formal coefficients, at appropriate
measurement horizons, with coherence using `Regular`. Use point positions,
extend by zero off configurations. Includes field and coupling transformations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Score
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open Dframe FVA2.Scale MS.Rake MS.Theater Level Facets Equator
variable { G:Gauge }{n m d k e:ℕ}
abbrev Album (G:Gauge):= (n:ℕ)→Points n→ Scan G n→ Cn
def install (A:Arenas G): Album G:= fun n x p=>if h:x∈conf n then Reg.Point.story ( A (totalG p) n ⟨x,h⟩ ) ( tape p (guardT p) ) else 0
def Regular ( A:Arenas G ): Prop:= ∀ d k (h:d≤k), FVA2.Scale.Inherited (A d) (A k) h
def Famous (A:Album G) : Prop:= ∀ n x (p:Scan G n), x∉ conf n→ A n x p=0
variable { A D: Arenas G }{ x:Points n }{ p: Scan G n }
abbrev test (A:Way G d)(x: FVA2.Scale.Stage n)(p:Scan G n)(h:Guarded p d):= Reg.Point.story ( A _ x ) ( tape p h )
lemma honored (he:Regular A)(hs:d≤k)(h:Guarded p d)(hx:x∈conf n): test ( A d ) ⟨x,hx⟩ p h=test ( A k ) ⟨x,hx⟩ p ( fun i=>(h i).trans hs ):= by ext i; rw [ test,test,Reg.Point.story,Reg.Point.story, coeff_mk, coeff_mk ]; exact he d k hs n _ _ _
lemma caring (p:Scan G n)(h:Guarded p d)(he:Regular A)(hx:x∈conf n): install A n x p=test ( A d ) ⟨x,hx⟩ p h:= by
    rw [install,dif_pos hx]; by_cases hh:d≤ totalG p; · exact Eq.symm ( honored he hh h hx )
    exact honored he (Nat.le_of_not_le hh) (guardT p) hx
lemma standardized : Famous (install A):= fun _ _x _p hp=> dif_neg hp
lemma regular_wave (u:ℝ){O:Booked (Press.portDeck G)}(T:MS_Data G O): Regular (wave u T):= fun _ _=> wave_walk u T
-- frame action.
variable {T:Frames G} {H:Guard G d}
lemma readyP (h:Guarded p d)(i: LivesP p): Guarded (decode p i) d:= h
lemma guard_status (V: ℕ→ Structure1.Point G d n)(ht:Civil T)(h: Guarded p d): Reg.Point.story ( status (T d) V ) ( tape p h )= ∑ j:LivesP p, play ( seats T ) p (decode p j) * Reg.Point.story V ( tape (decode p j) ( readyP h j ) ):= by
    ext i; unfold Reg.Point.story play; rw [coeff_mk,map_sum]; simp_rw [ Constants.admits,coeff_mk ]; rw [ seen, Finset.sum_comm ]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold pulseU tape; simp_rw [ cap_map ht ]; rw [( V (j none) ).map_sum ]; simp_rw [( V ( j none ) ).map_smul_univ]; rfl
abbrev marking (T:Cast G)(A:Album G): Album G:= fun n x v=> concert T v ( A n x )
abbrev Mark (T:Frames G)(A:Arenas G): Arenas G:= fun d=> actMark ( T d ) ( A d )
lemma marks (he: Regular A)(ht:Civil T): Regular ( Mark T A ):= fun _ _ h=> unfold_acts _ _ h _ _ ( he _ _ h ) ( ht.growth h )
lemma unveil (he: Regular A)(ht:Civil T): marking (seats T) (install A)= install ( Mark T A ):= by
    funext n x v; by_cases hx:x∈ conf n; swap; · simp [ marking,install,hx,concert ]
    rw [ caring v ( guardT v ) ( marks he ht ) hx ]; unfold marking Mark concert test actMark; simp_rw [ show ∀ i:LivesP v, install A n x (decode v i)= _ from fun i=> caring ( decode v i ) (readyP (guardT v) i) he hx ]; exact Eq.symm ( guard_status _ ht (guardT v) )
-- coupling
variable {p':Cn}
abbrev tune (p:Cn)(A:Album G): Album G:= fun n x v=> ( A n x v ).subst p
abbrev TuneQ (p:Cn)(A:Arenas G): Arenas G:= fun d=> couple p ( A d )
lemma tune_reg (he:Regular A): Regular ( TuneQ p' A ):= fun _ _ h=> Facets.unfold_team _ p' h _ ( he _ _ h )
lemma tune_live (h:Rooted p'): tune p' ( install A )= install (TuneQ p' A):= by
    funext n x v; unfold tune install; split; · exact ( Reg.Point.moves _ _ h ).symm
    rw [ ← PowerSeries.coe_substAlgHom (Reg.Choice.licence p' h), map_zero ]
variable {ν:ℝ}
lemma stock (u:ℝ){O:Booked (Press.portDeck G)}(T: MS_Data G O)(p:Scan G n)(hx:x∈conf n)(k:ℕ): coeff k (install (wave u T) n x p)= Dial.tour T p u (fun i=> Theater.out ( x i )) Finset.univ k:= by
    rw [install,dif_pos hx]; unfold Reg.Point.story; rw [coeff_mk]; exact Dframe.ribbon u ( t:=fun i=> low ( p i ) ( guardT p i ) ) T x k
end YM.FVA2.O.Score
