import YM.FVA2.DerivD.Plant
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
 # Nested multi label shuffle-factorized law for first gradients
   Cast matrix may act at all orders, first slot a single label.
 -/
open O.Read
variable { I: Type }{G:Gauge}{n m d k:ℕ}{ F:Arenas G }{ g:Cn }{ x: Points n }
abbrev Using (v:Scan G n)(p:Q G):= Fin.append v (Single p)
variable (T U: Cast G)(P R:Staff G)(a:Axis)
-- staff stored indexed as row, compatible Score matrix convention. thus N P M? for E^W satisfies J_W * M = M * J_E
abbrev χ (v:Axis)(P:Staff G)(d:ℕ): Matrix (Grade G d) (Grade G (d+1)) Cn:= fun i j=> P (own i) v j
def altered (T U:Cast G) (P: Staff G) : Staff G:= fun p v j=> ( (T p.h)* χ v P p.h * ( U (p.h+1) ) ) p.item j
variable {T U} (h:U*T=1)
lemma prices (h':U*T=1)(d:ℕ): χ a ( altered T U P ) d * T (d+1) = (T _)* χ a P d:= by
    change ( ( T d )* χ a P d * (U (d+1)) )*( T (d+1) )=_; rw [ Matrix.mul_assoc _ ( U (d+1)), show (U (d+1)) * ( T (d+1) )=1 from congr_fun h' _, Matrix.mul_one ]
lemma solus (y: Scan G 1→Cn)(i:Fin 1)(p:Q G): Raise P i a ( Single p ) y=∑ j: Grade G ( heft p+1 ),P p a j * y ( Single (own j) ):= by
    unfold Raise; change ( ∑ i',_ )=_; refine Finset.sum_congr rfl fun j _=>?_ ; rw [ show update ( Single p ) i (own j)=Single (own j) from funext fun k=> (by rw [ Subsingleton.elim k i, update_self ]) ]
-- base contour. single
include h
lemma variant (p:Q G)(y:Scan G 1→Cn)(i:Fin 1): Raise ( altered T U P ) i a ( Single p ) ( fun j=> concert T j y )= concert T ( Single p ) ( fun j=> Raise P i a j y ):= by
    rw [ solus ]; simp_rw [ O.Score.solo,solus ];
    let E := χ a ( altered T U P ) p.h; let X:Grade G (p.h+1)→Cn:= fun i=> y ( Single (own i) );
    change (E *ᵥ ( T _ *ᵥ X ) ) p.item= (T _ *ᵥ (χ a P _ *ᵥ X )) p.item; rw [ Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, prices _ _ h ]; -- orientation
omit h
lemma duet (p:Scan G n)(q:Scan G m)(y:Scan G (n+m)→Cn): concert T ( Fin.append p q ) y = concert T p ( fun s=> concert T q ( fun t=> y ( Fin.append s t ) ) ):= O.Score.splits .. -- maybe name `O.Score`
lemma comm (p:Scan G n)(q:Scan G m)(F: Scan G n→ Scan G m → Cn)(i:Fin n): concert T q ( fun t=> Raise P i a p ( fun v=> F v t ) )=Raise P i a p (fun v=> concert T q ( F v ) ):= by
    unfold concert Raise; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum]; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> mul_left_comm ..
lemma mix_side (p:Scan G n)(q:Scan G m)(f:Scan G (n+m)→Cn)(i:Fin n)(he:∀ (y: Scan G n→Cn), Raise ( altered T U P ) i a p (fun s=> concert T s y)=concert T p ( fun j=> Raise P i a j y )): Raise ( altered T U P ) ( Fin.castAdd m i ) a ( Fin.append p q ) (fun j=> concert T j f)=concert T ( Fin.append p q ) ( fun j=> Raise P ( Fin.castAdd _ i ) a j f ):= by
    rw [append_scale]; simp_rw [ duet (T:=T), he _, ← comm,append_scale ]; -- arguments order
lemma stage_r (p:Scan G n)(q:Scan G m)(f:Scan G (n+m)→Cn)(i:Fin m)(he:∀ (y: Scan G m→Cn), Raise ( altered T U P ) i a q (fun s=> concert T s y)=concert T q ( fun j=> Raise P i a j y )): Raise ( altered T U P ) ( Fin.natAdd n i ) a ( Fin.append p q ) (fun j=> concert T j f)=concert T ( Fin.append p q ) ( fun j=> Raise P ( Fin.natAdd _ i ) a j f ):= by
    rw [append_phase]; simp_rw [ duet (T:=T), ← comm,he _, append_phase ]; -- need commute Raise q through outer
include h
lemma savvy (p:Scan G n)(f:Scan G n→Cn)(i:Fin n): Raise ( altered T U P ) i a p (fun j=> concert T j f)=concert T p ( fun j=> Raise P i a j f ):= by
    induction n with
    | zero=> exact Fin.elim0 i
    | succ n IH=>
       generalize hz : p = f' at *; rw [ ← correct f' ]; induction i using Fin.addCases with
       | left i=> exact mix_side P a _ _ _ _ fun _=> IH .. -- adjust
       | right i=> apply stage_r P a; intro t; rw [show right0 f'=Single (f' ( Fin.natAdd n i )) from funext fun j=> by rw [Subsingleton.elim j i]; rfl ]; exact variant P a h _ _ i
end YM.FVA2.DerivD
