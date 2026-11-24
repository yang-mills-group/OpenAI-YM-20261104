import YM.FVA2.DerivD.Staff
import YM.FVA2.DerivD.Tour
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
# Identify physical-alphabet derivatives on the MS continuum arrays

Each axis derivative of a field gives a formal combination of fields one grade higher;
use the existence/preparation from `Extras.ambiguity` on these specific operators.
`inspiration`: this gives the influence law under derivatives of the positions,
retaining all other marks. All in the supplied MS scheme.
-/
open Smooth Lifetime Smooth.Cruise Smooth.Slots O.Ward O.Lives Extras
open Dframe
variable {G:Gauge}{n:ℕ}
local notation "𝔓"=> (Press.portDeck G)
variable {B:Booked ( Press.portDeck G )}(a:ℝ)(M:MS_Data G B)
def J (v:Q G)(i:Axis): T (Extras.Package 𝔓 (heft v+1)):= Classical.choose (( ambiguity ( safe ( u:=a ) (M:=M) v [i])).exists) -- h binder?
abbrev knownT (u:Q G)(i:Axis):= Says a M ( J a M u i ) ( beamH M ( Tide.frameF Unit a ) u [i] )
lemma informed (u:Q G)(i:Axis): knownT a M u i := Classical.choose_spec (( ambiguity ( safe ( u:=a ) (M:=M) u [i] ) ).exists)
def authority : Staff G:= fun u i h=> PowerSeries.mk ( fun k=>( J a M u i k h:ℂ ) )
-- evaluate M's assigned derivative for one slot.P.Arg order
variable (u:Scan G n)(i:Fin n)(v:Axis)(x:Points n)(hx:x∈conf n)
local notation "F₀"=> (Tide.frameF Unit a)
local notation "X"=> ( install (Equator.wave a M) )
def outlined (n:ℕ): Points n→L[ℝ] Draw (Fin n):= ContinuousLinearMap.pi ( fun i=> Theater.out.toContinuousLinearEquiv.toContinuousLinearMap ∘L ( PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin n=> E4) i ) )
lemma outline (x:Points n) (i:Fin n) : outlined n x i= Theater.out (x i):= rfl
include hx
lemma overlap : Function.Injective (outlined n x):= Theater.out.injective.comp hx
lemma varV (k:ℕ): Music a M u ( Smooth.hop plain (i,v) ) ( outlined n x ) Finset.univ k= coeff k ( Raise (authority a M) i v u ( X n x ) ):= by
    let s:= Smooth.hop plain (i,v); let Y:= Slots.att F₀ M u s; let V : MS.Rake.Position (Fin n) Unit := fun i (_:Unit)=> Theater.out (x i); obtain hP:= touch (a:=a) ( overlap x hx ); have hZ : Extras.Survey F₀ M Y V:= fun i=> Extras.Estate ( safe _ _|>.2 ) ( safe _ _|>.1.1 ) _;
    rw [notation_t ( overlap x hx )]; change service a M Y V _ _=_; rw [informed a M (u i) v (Fin n) inferInstance V Y i ?_ hZ hP Finset.univ ( Finset.mem_univ _ ) (fun j _=> (safe _ _|>.1)) k ]; unfold Raise; simp_rw [ LinearMap.coe_mk, AddHom.coe_mk,map_sum, coeffF ]; refine Finset.sum_congr rfl (fun j _=> Finset.sum_congr rfl fun k' h=>?_ ); rw [authority,coeff_mk, stock _ _ _ hx ]; refine congr_arg₂ (·*·) rfl (Extras.tourC ( swapped hZ j i ) hP _ ?_ _ _ );
    · funext w; by_cases he:w=i; subst w; rw [swapField,Function.update_self, Function.comp_apply,Function.update_self]; rfl
      unfold swapField; rw [ Function.update_of_ne he, Function.comp_apply, Function.update_of_ne he ]; unfold Y Slots.att s Smooth.hop; rw [ Function.update_of_ne ( show w≠(i,v).1 from he ) ]; rfl
    unfold Y Slots.att s; rw [ Smooth.hop,Function.update_self ]; rfl
omit hx
protected lemma inspiration : Influence (authority a M) X:= by
    intro n x hx u k; let p:=outlined n; obtain hp : Function.Injective (p x):= overlap x hx;
    have hQ:= (realMusic hp Finset.univ k a M u plain).comp x p.hasFDerivAt; apply HasFDerivAt.congr_of_eventuallyEq ( f:=fun (x:Points n)=> Music a M u plain ( p x ) Finset.univ k ) _ ?hp ; swap; · exact Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( conf_open n ) hx ) (fun y hy=> Eq.trans ( stock a M u hy k ) ( by rw [symbolic ( overlap _ hy )]; rfl ));
    refine HasFDerivAt.congr_fderiv hQ ?_; ext1 y; simp_rw [_root_.sum_apply, appears, ContinuousLinearMap.comp_apply, Abroad.ray, ← varV a M u _ _ x hx ]; simp_rw [one_mul]; rfl
end YM.FVA2.DerivD
