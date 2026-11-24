import YM.QuadraticLocal.Poetry.Agenda
/-!
# Algebra for publishing stamps before current photos. Resolution of Spectator role field. Width.
 Use with Φ.Document later. Mint Lumi.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Sunrise.Aviary Stationary Picket
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type} [Nonempty ι] [Fintype M] [Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M)(I:M→ Loan) {a C D b:ℝ} {n m:Side}{k d N l:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Agenda
variable {Γ:ι→ℝ}
local notation "J"=> Link G n
local notation "P"=> (Fin d)
local notation "W"=> rule (Coarse G⊕M) n
-- V rank.Pay.PostPicture plus snapshot. Commercial audits.News.C.F. Along Vernal.
variable {X Y: Book (Stationary.Link G n)}(S:Finset α){F:α→Book (Stationary.Link G n)}
local notation "λ'" e:max=> guard I H e
lemma v_plus {k:ℕ}(X':Vernal G n X k)(Y':Vernal G n Y k)(hX:∀ j≤k,Plausible (X j))(hY:∀ j≤k,Plausible (Y j)) : Vernal G n (X+Y) k ∧ ∀ j≤k,Plausible ((X+Y) j):= by
 have hx(v:ℝ→J)(ht:ContDiffAt ℝ ω v 0): weigh v (X+Y) k= weigh v X k+weigh v Y k:= weigh_add ht (fun i hi=> (hX i hi).smooth.contDiffAt) (fun i hi=> (hY i hi).smooth.contDiffAt) le_rfl
 refine ⟨⟨fun u v w x hu hv hH he=> ?_⟩,fun j hj=> (hX j hj).add (hY j hj)⟩; rw [hx u hu,hx v hv,X'.leaf u v w x hu hv hH he,Y'.leaf u v w x hu hv hH he]
lemma v_empty (k:ℕ)(n:Side): Vernal G n 0 k ∧ ∀ j≤ k,Plausible (fun _:Link G n=>(0:ℝ)):= by
 refine ⟨⟨fun u v w x hu hv hH he=> ?_⟩,fun _ _=> Plausible.atom _⟩; rfl
lemma v_pile (hp:∀ i∈S,Vernal G n (F i) k)(hv:∀ i∈S,∀ j≤k,Plausible (F i j)) : Vernal G n (∑ i∈S,F i) k∧∀ j≤k,Plausible ((∑ i∈S,F i) j):= by
 induction S using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact v_empty _ _
 | insert i s hi ih=> obtain ⟨hl,hh⟩:= ih (fun i hx=> hp i (Finset.mem_insert_of_mem hx)) (fun i hx=> hv i (Finset.mem_insert_of_mem hx)); rw [sum_insert hi]; exact v_plus (hp i (mem_insert_self ..)) hl (hv i (mem_insert_self ..)) hh
lemma lamp_s {f:Ink.Field (Coarse G⊕M)}(he:f.Good a C k)(ht:0 ≤ a)(v:rule M n) : Plausible (fun x:Link G n=> f.table n (mingle x v)):= by
 let W':= (desks (Coarse G) M n).symm.toContinuousLinearMap; let a:= mingle (0: Link G n) v; let B:= W' ∘L ContinuousLinearMap.inl ℝ (Link G n) (rule M n); have hz(i:Link G n): mingle i v=a+B i:= by rw [show mingle i v= W' ((0,v)+(i,0)) from (by simp; rfl),_root_.map_add]; rfl
 simp_rw [hz]; exact ((he.binding (n:=n) ht).2.1.app B a).read
-- Equation.
end Agenda
end YM.QuadraticLocal.Poetry
