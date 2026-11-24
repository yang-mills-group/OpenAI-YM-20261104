import YM.FVA2.Generator.Cycle
/-!
 # Grade adjustment by the *generator* prescription

 Preliminaries differentiating turner as `Instant` even prior to same-degree tests.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
local notation "L" => FieldEnd G d
/- `𝖽` in §kfar. -/
def bill (d:ℕ) : FieldEnd G d:= ∑ i:E d, ( i.val:ℂ ) • proj i
local notation "𝕕" => (bill ( G:=G ) d)
lemma on_point (p: Sec G d)(i:E d): 𝕕 (proj i p)=(i.val:ℂ) • proj i p:= by
    unfold bill; rw [ LinearMap.sum_apply ]; simp_rw [LinearMap.smul_apply]; rw [Finset.sum_eq_single i]; · rw [again]
    · intro j _ Hj; rw [Level.distinct p j i Hj,smul_zero]
    simp
lemma at_grade (p: Sec G d)(i:E d): proj i (𝕕 p)=( i.val :ℂ ) • proj i p:= by
    conv=> lhs; arg 2; rhs; rw [ ← Level.all p ]; skip
    rw [map_sum,map_sum]; simp_rw [on_point,_root_.map_smul]; rw [ Finset.sum_eq_single i ]; · rw [again]
    · intro j _ Hj; rw [Level.distinct p i j Hj.symm,smul_zero]
    simp
lemma intrinsic_clock : Instant (fun t=> PowerSeries.C ( Level.Dial d t )) (-(PowerSeries.C 𝕕)) 0:= by
    intro i v; by_cases h:i=0; swap
    · simp only [map_neg,coeff_C, if_neg h,map_zero,neg_zero]; exact hasDerivAt_const ..
    simp only [map_neg,h,coeff_C, ↓reduceIte, Level.Dial, bill,map_sum, _root_.map_smul,smul_eq_mul]; rw [ ← Finset.sum_neg_distrib ]; simp_rw [ ← neg_mul ]; apply HasDerivAt.fun_sum; intro j _; refine HasDerivAt.mul_const ?_ _; unfold Extent.token; obtain hp:= (hasDerivAt_id' (𝕜:=ℝ) 0).neg.exp.ofReal_comp.fun_pow j.val; simpa using hp
variable (A:Guard G d)
lemma turn_cost (t:ℝ): convertT t A=C (Level.Dial d (-t))*A*C (Level.Dial d t):= by
    refine PowerSeries.ext fun i=>?_ ; rw [ coeff_mul_C, coeff_C_mul ]; exact coeff_mk .. -- defeq?
lemma neutral : convertT 0 A=A:= by rw [ turn_cost ]; simp only [neg_zero, Level.flat,map_one,mul_one,one_mul]
lemma rev_clock : Instant (fun t=> PowerSeries.C ( Level.Dial d (-t) )) (PowerSeries.C 𝕕) 0:= by
    intro i v; obtain h' := intrinsic_clock i v; have hv: HasDerivAt (fun x:ℝ=> - x) (-1) 0:= (hasDerivAt_id' (𝕜:=ℝ) 0).neg; rw [ ← neg_zero (G:=ℝ) ] at h'; obtain h:= h'.scomp 0 hv; simpa only [ map_neg, neg_zero,Function.comp_def, neg_smul, one_smul,neg_neg ] using h
lemma steady : Instant (fun _=> A) 0 0:= by intro i v; rw [ map_zero,map_zero ]; exact hasDerivAt_const ..
/-- $[𝖽, T]$ arises in infinitesimal generator. -/
def weight : Guard G d:= C 𝕕 * A- A * C 𝕕
lemma applyD : Instant (fun t=> convertT t A) (weight A) 0 := by
    have hz {A : Type} [Ring A] (x y:A): -(x*y)=x*(-y) := (_root_.mul_neg ..).symm
    simp_rw [turn_cost]; obtain H:= combine (combine rev_clock ( steady A ) ) ( intrinsic_clock (d:=d) ( G:=G ) ); simp only [ neg_zero, Level.flat,map_one,add_zero,one_mul,mul_one,mul_zero ] at H; 
    unfold weight; rw [ sub_eq_add_neg,hz A (C 𝕕) ]; exact H
open Dframe
variable (p:Sec G d)(i j:E d)
private abbrev Δ (i j:E d):ℂ:= ( ↑(i.val):ℂ )-( ↑(j.val):ℂ )
lemma spread (n:ℕ): proj i (coeff n (weight A) (proj j p))=Δ i j • proj i (coeff n A (proj j p)):= by
    unfold weight; rw [ _root_.map_sub, LinearMap.sub_apply,_root_.map_sub, coeff_C_mul,coeff_mul_C, Module.End.mul_apply, Module.End.mul_apply, at_grade,on_point, _root_.map_smul,_root_.map_smul]; exact Eq.symm (@sub_smul ℂ (Sec G d) _ _ _ _ _ (proj i (coeff n A (proj j p))))
lemma grade_drop (n:ℕ) : Level.diag (coeff n (weight A))=0:= by
    ext1 p; rw [ ← Level.all p,map_sum ]; simp_rw [ diagonals, spread,Δ, sub_self,zero_smul, Finset.sum_const_zero, LinearMap.zero_apply ]
lemma height (n:ℕ)(hp:Level.diag (coeff n A)=0)(h:Graded (coeff n (weight A))): coeff n A=0:= by
    ext1 p; rw [ ← Level.all p,map_sum,LinearMap.zero_apply ]; apply Finset.sum_eq_zero; intro i _; rw [ ← Level.all ( coeff n A ( proj i p ) ) ]; apply Finset.sum_eq_zero; intro j _; by_cases he:j=i; · subst j; rw [ ← diagonals,hp,LinearMap.zero_apply ]
    apply smul_right_injective (Sec G d) (r:= (Δ j i)) (sub_ne_zero_of_ne (show ( ↑(j.val):ℂ )≠ (↑(i.val):ℂ) from fun h=> he ( Fin.ext (by exact_mod_cast h)))); dsimp only; rw [ ← spread,smul_zero, ← ( h : _=_ ), grade_drop,LinearMap.zero_apply,map_zero ]
end YM.FVA2.Clef
