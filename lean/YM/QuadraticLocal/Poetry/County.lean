import YM.QuadraticLocal.Poetry.Plates
/-!
# Publish field transfer from one & ANY renewed lantern at a printed grade
 enough widths for next step. table IF needed. heights ≤n.App.K.Scope.Wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d e j N:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Garnish
-- stack with Miller witness.K all tag.Born.S.Space. applies any Halo owner.Coordinate R.A.
open Picket Rovers
open AllOrder.Ink.Field
local notation "Q"=> (α⊕M)
def stack (F:Ink.Field α)(s:List (Point M)) : Ink.Field (α⊕ M) where
 Ty := F.Ty
 fee := F.fee
 slip i:= List.map (Prod.map id Sum.inl) (F.slip i) ++ swallow α s
lemma props (s:List Z)(p:Slip (Point α)) : primary ((List.map (Prod.map id Sum.inl) p)++swallow α s)=p ∧ second (List.map (Prod.map id Sum.inl) p ++ swallow α s)=s:=by
 have he(x:List Z): primary (swallow α x)= ([]:List (Point α))∧second (swallow α x)=x:= by
    induction x with | nil=> exact ⟨rfl,rfl⟩ | cons v x ih=> refine ⟨ih.1,?_⟩; exact congr_arg (v::·) ih.2
 induction p with | nil=> exact he s | cons v p ih=> refine ⟨?_,ih.2⟩; exact congr_arg (v::·) ih.1
variable (S:List (Point M))(F:Ink.Field α)
local notation "T"=> stack F S
lemma metropolis (i:(stack F S).Ty) : primary ((T).slip i) = F.slip i ∧ second ((T).slip i)=S:= props S (F.slip i)
lemma license (h:F.Good a C k) : (T).Good a (Real.exp (a*meter S)*C) (k+S.length) := by
 refine ⟨fun i=> by let he:=h.length i; rw [size_at _, (metropolis S F i).1,(metropolis S F i).2]; exact Nat.add_le_add_right he _, ?_⟩
 rw [show (stack F S).price a=(fun i:F.Ty=> Real.exp (a*meter S)*F.price a i) from funext fun i=> by unfold Field.price; rw [meter_at, (metropolis S F i).1,(metropolis S F i).2, Nat.cast_add,mul_add,Real.exp_add]; change _ * |F.fee i|= _; ring]; exact Push.Local.sumBudget_mul_left h.pay (Real.exp_pos _).le
lemma regard (x:Site n)(v:rule α n)(u:rule M n): (stack F S).site n x (mingle v u)=(F.site n x v)*Ink.invoice x S u:= by
 let f(i:Point α):= v (Ink.stood x i); let g (i:Point M):= u (Ink.stood x i); unfold Field.site; rw [←tsum_mul_right]; change (∑' i:F.Ty, F.fee i* _)= _; apply tsum_congr; intro i; rw [mul_assoc]; apply congr_arg (F.fee i*·); let L:=(T).slip i; have h : mingle v u ∘ (stood (α:=Q) x) = fun i:Point (α⊕M) => i.2.elim (fun z=>f (i.1,z)) (fun z=>g (i.1,z)):= by ext1 i; rcases i with ⟨p,i|i⟩ <;> rfl
 let Z' := Rovers.spent f g L; rw [show L=_ from (show L=(T).slip i from rfl),(metropolis S F i).1,(metropolis S F i).2,← h] at Z'; simpa only [Ink.invoice,paid,List.map_map,f,g,Function.comp_def] using Z'
lemma attire (hh:Depicted H (swallow α S))(hg:(0,q)∈S): Fixed H q (stack F S):= by
 refine ⟨fun i j=>?_,fun i=>?_⟩; · rw [← Rovers.flushed, (metropolis S F i).2]; exact hh _
 apply (Rovers.knows (0,q) _).1; rw [(metropolis S F i).2]; exact hg
-- Void ownership.
lemma wash (H:Finset M) (q:M): Fixed H q (Field.void (α⊕ M)):= ⟨fun i=> (nomatch i),fun i=>(nomatch i)⟩
end Garnish
namespace Dais
open Picket
variable (T:Atom G k)(r:ℕ)
local notation "W" v=> Dais.field v G
def plain (d:ℕ): Side:= ⟨8*d+1,by omega⟩
def torch : AllOrder.Ink.Field (Coarse G):= Plaza.tile (Dais.field T.length G) (0:Site (plain T.length)) r (Helmet.frame T 0)
lemma noted (x:Site n): (torch T r).site n x= Radial.jet (Helmet.frame T x) r:= Plaza.talks _ x _ _ _ _ (by exact Dais.width _ (Nat.lt_succ_self _)) (fun v w h=> talk T x 0 (le_refl T.length) h) (spends T (0:Site (plain T.length)) r).analytic
local notation "Λ"=> Fintype.card G.ColorIndex
set_option quotPrecheck false
local notation "ζ"=> (W T.length).card
open Comparison.Density.Render
lemma power (b:ℝ)(hb:0<b) : (torch T r).Good b (((ζ:ℝ)^r)*( Real.exp (b*(r*(4*T.length):ℕ)) * ((Fintype.card G.ColorIndex+1:ℝ)^r*Comparison.Density.Render.fareAt T r))) r:= by rw [← Nat.cast_pow]; exact Plaza.pilot _ _ _ _ (spends T _ r) _ hb.le (fun i h=>FreeResolvent.Lifted.fit_box i.1 T.length (mem_product.mp h).1)
-- remove norm_cast
end Dais
end YM.QuadraticLocal.Poetry
