import YM.X.Braid.Stitch
import YM.Next.RANK.Crust
/-!
# Single-vs-multi Ward contact. Finite projector equations for local ambiguity.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric
open Reed
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {V:Type*} {n m:ℕ}
local notation "P"=> Normal.poly V
local notation "R"=> V →₀ ℂ
variable (Q:Symmetric V)(r:V→V→₀ℂ)
def tilt : Derivation ℂ P P:=MvPolynomial.mkDerivation ℂ (glyph ∘ r)
def hair (i:V):= slit (Pi.single i 1)
lemma tilt_point (i:V): tilt r (X i)=glyph (r i):= by simp [tilt]
lemma tally (p:P)(u:Finset V)(h:p.vars⊆u): tilt r p =∑ i∈u,glyph (r i) * hair i p:= by
    let L: Derivation ℂ P P := ∑ i∈u, glyph (r i) • hair i
    have he(i:P): L i = ∑ j∈u,glyph (r j)*hair j i := by
        unfold L; clear h; induction u using Finset.induction_on with
        | empty=> rw [Finset.sum_empty,Finset.sum_empty];rfl
        | insert j s hj IH=> rw [Finset.sum_insert hj, Finset.sum_insert hj,Derivation.add_apply,IH];rfl
    rw [← he]; apply MvPolynomial.derivation_eq_of_forall_mem_vars; intro i hi; rw [he,tilt_point]; simp [hair,Pi.single_apply,h hi]
lemma ringK (p:P)(u:Finset V)(h:p.vars⊆u):
     milk Q (tilt r p) - tilt r (milk Q p)=∑ i∈u,edge Q (r i) (milk Q (hair i p)):= by
    rw [tally _ p u h, map_sum, tally r (milk Q p) u ((Tapes.milk_vars ..).trans h),← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _=>?_ ; unfold hair; rw [skims,refresh,← skims]; rw [add_sub_cancel_left]; rfl
lemma hair_free {p:P}{i:V}(h:i∉p.vars):hair i p=0:=by apply derivation_eq_zero_of_forall_mem_vars; intro j hj; simp [hair, show j≠i from ne_of_mem_of_not_mem hj h]
variable {p q:Normal.poly V}
/-- chi cutoff weights as explicit enumeration Finset; excludes aliases. `A` is total cubic cutoff sum. `S` is its shell quadratic response. -/
lemma kurot (m:V→ℂ)(A S:P) (g:V→V→₀ℂ)(χ:V→ℂ)(t:Finset V)
    (h₀:slit m p=0)(h:slit m q= -tilt r p)(hA: slit m A = -(∑ i∈t,χ i • (glyph (g i)*glyph (r i))) - S) (he:p.vars ⊆ t)(hc:∀ i∈p.vars,χ i=1)(hQ:∀ i∈t,edge Q (g i) p=hair i p):
    slit m (milk Q q - multi Q (milk Q p) A) = -tilt r (milk Q p) + multi Q (milk Q p) S := by
    let P₀:= milk Q p
    have hP:slit m P₀=0:= by unfold P₀; rw [skims,h₀,map_zero]
    change _=_+multi Q P₀ S; rw [map_sub,ms,skims m Q q,h, map_neg,hA,hP]
    have ht (x:P): multi Q 0 x=0:= by change toned Q 0 x=0; rw [map_zero]; rfl
    have hk (x:P): multi Q P₀ x= toned Q P₀ x:=rfl
    change -(milk Q (tilt r p))-(multi Q 0 A+multi Q P₀ _)= _
    rw [ht,hk,map_sub,_root_.map_neg,map_sum]; change _= -tilt r P₀ + _; rw [hk,zero_add]
    have he':∑ i∈t, toned Q P₀ (χ i • (glyph (g i)*glyph (r i)))=∑ i∈t,edge Q (r i) (milk Q (hair i p)):= by
       refine Finset.sum_congr rfl fun i hi=> ?_ ; rw [map_smul]; change _ • multi Q P₀ (glyph _*_)=_; rw [m2, show edge Q (g i) P₀= milk Q (hair i p) from (skims _ Q p).trans (congr_arg (milk Q) (hQ i hi))]; by_cases hv: i∈p.vars; · rw [hc _ hv,one_smul]
       rw [hair_free hv,map_zero,map_zero,smul_zero]
    rw [he',← ringK Q r p t he]; unfold P₀; abel
end YM.PositionX.Braid
