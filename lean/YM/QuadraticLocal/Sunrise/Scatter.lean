import YM.QuadraticLocal.Sunrise.Heat
import YM.QuadraticLocal.Fk.Ballot
import Mathlib.Algebra.MvPolynomial.Funext
/-!
# Put scalar extra fields onto the real tag monomial algebra

Uniform exponent `h` for charging occurs in its own color dictionary,
not a guessed truncation of Mark.Designed for use in delivering equality at *each* regulator even
small apertures. Doesn't claim Bounds yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Topology Classical ContDiff
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I] (J:Census V)
variable (p:I→ Poly J)
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
local notation "φ"=> I→ℝ
local notation "M"=> MvPolynomial I ℝ
local notation "χω"=> (I→ℝ)×Y
local notation "ξ"=> Poly J
local notation "ν"=> Poly.bead J
open MeasureTheory
variable {f g:(I→ℝ)→ℝ} {T: ((I→ℝ)×Y)→ ℝ}
-- polynomial class and choose.Have separability for Plan.N. & integration.
namespace Scatter
-- use lowercase proof.Lens
open MvPolynomial
-- funext MvPolynomial ambiguous
variable {K N:MvPolynomial I ℝ}
def chart (f:(I→ℝ)→ℝ)(K:MvPolynomial I ℝ):Prop:=∀ i,f i= MvPolynomial.eval i K
lemma line (L: (I→ℝ) →ₗ[ℝ] ℝ): chart (⇑L) (∑ i:I,C (L ((Pi.basisFun ℝ I) i)) * MvPolynomial.X i) := by
    intro z; rw [map_sum]; simp_rw [map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]; conv_lhs => rhs; rw [←(Pi.basisFun ℝ I).sum_repr z];
    rw [map_sum]; apply sum_congr rfl fun i _=> ?_; rw [map_smul]; change _ * L _ = _; rw [Pi.basisFun_repr,mul_comm]
lemma beam (i:I): chart (fun x=>x i) (MvPolynomial.X i):=fun _=> (eval_X ..).symm
lemma color (v:ℝ): chart (fun (_:I→ℝ)=>v) (MvPolynomial.C v):= fun _=> (eval_C ..).symm
lemma add (hf:chart f K)(hg:chart g N): chart (f+g) (K+N):= by intro i; rw [map_add,Pi.add_apply,hf,hg]
lemma multiply (hf:chart f K)(hg:chart g N): chart (f*g) (K*N):=by intro i; rw [map_mul,Pi.mul_apply,hf,hg]
lemma raise (t:ℝ) (hf:chart f K): chart (t•f) (MvPolynomial.C t*K):= multiply (color t) hf
lemma repr_f (hf:Plausible f):∃ p, Scatter.chart f p:= by
    induction hf with
    | atom v=>exact ⟨_,color _⟩
    | times g a ha ih=> exact ⟨_,multiply ih.choose_spec (line a)⟩
    | add _ _ i j=> exact ⟨_,Scatter.add i.choose_spec j.choose_spec⟩
lemma unique (hf:chart f K)(ht:chart f N): K=N:= MvPolynomial.funext (fun x=> (hf x).symm.trans (ht x))
local notation "χ"=> Fk.Ballot.inc J
variable (f)
def reprP : MvPolynomial I ℝ:=if h:∃ e,chart f e then h.choose else 0
variable {f}
lemma signal (h:chart f K): reprP f=K:=by unfold reprP; rw [dif_pos (show ∃ e,chart f e from ⟨_,h⟩)]; exact unique (show chart f _ from Exists.choose_spec _) h
variable (f)
def transmit := MvPolynomial.eval₂Hom χ p (reprP f)
variable {f}
local notation "ϕ"=> transmit J p
lemma sent {F: MvPolynomial I ℝ} (h:chart f F): ϕ f=eval₂Hom χ p F:=by unfold transmit; rw [signal h];
variable {p J}
lemma constant (v:ℝ): ϕ (fun _=>v)=ν (↑v:ℂ):= by rw [sent _ _ (color v), eval₂Hom_C]; rfl
lemma factor (i:I) : ϕ (fun x=>x i)=p i:= by rw [sent _ _ (beam i)]; exact eval₂_X .. 
lemma sends (hf:Plausible f)(hg:Plausible g): ϕ (f+g)=ϕ f+ϕ g:=by
   obtain ⟨K,hK⟩:= repr_f hf; obtain ⟨U,hU⟩:= repr_f hg; rw [sent _ _ (Scatter.add hK hU), sent _ _ hK,sent _ _ hU,map_add]
lemma carry (hf:Plausible f)(hg:Plausible g): ϕ (f*g)=ϕ f*ϕ g:=by
   obtain ⟨K,hK⟩:= repr_f hf; obtain ⟨U,hU⟩:= repr_f hg; rw [sent _ _ (Scatter.multiply hK hU), sent _ _ hK,sent _ _ hU,map_mul]
variable (J p)
lemma chars : ϕ (0:(I→ℝ)→ℝ)=0:=by exact (Scatter.constant (J:=J) (p:=p) 0).trans (by simp)
lemma one : ϕ (1:(I→ℝ)→ℝ)=1:=by exact (Scatter.constant (J:=J) (p:=p) 1).trans (by simp)
lemma mul (t:ℝ)(hf:Plausible f): ϕ (t•f)= (↑t:ℂ) • ϕ f:=by
   rw [show t • f=(fun (_:I→ℝ)=> t)*f from rfl, carry (Plausible.atom _) hf, constant, Poly.product_bead] -- direction
lemma pile {ζ:Type*} (s:Finset ζ) {f:ζ→(I→ℝ)→ℝ}(hf:∀ i∈s,Plausible (f i)): ϕ (∑ i∈s,f i)=∑ i∈s,(ϕ (f i)):=by
 induction s using Finset.induction_on with
 | empty=>simp [chars]
 | insert i s hi ih=> rw [Finset.sum_insert hi,sum_insert hi, sends (hf i (Finset.mem_insert_self ..)) (Plausible.sum (fun j hj=>hf _ (Finset.mem_insert_of_mem hj))), ih (fun j hj=> hf _ (Finset.mem_insert_of_mem hj))]
end Scatter
end YM.QuadraticLocal.Sunrise
