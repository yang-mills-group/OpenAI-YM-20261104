import YM.RGLocalTaylor.Retain.Inherits
/-!
# Telescoping products BEFORE common integration
Full mixed Lipschitz estimate for hypothetical faded log Snippet replacement.
Aims specifically at ANY normalized remainder in the supplied input physics,
retaining the gauge state / trajectory, budget about x. No parameter
interpretation for the telescope, in particular not granting any input
bound on modeled-kernel substitutions. Includes one postage per Head and
`brush` bounds through V-derivatives of all power Taylor columns, propagated
across Torso. No weakening of hierarchical growth through cost sharing.Holds
nonperturbative histories unchanged along the estimate. See Retain Ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Insert
variable (a : ℝ)
def sumTwo (f f' : Insert T) : Insert T:= ⟨fun {_} X z=> f.value X z+f'.value X z⟩
def shrink (f :Insert T)(a:ℝ):Insert T:= f.mapSmooth (fun v=> a*v)
def difference (f f' : Insert T): Insert T:= f.sumTwo (f'.shrink (-1))
lemma gap (f f':Insert T)(X:Coat T F)(z:Air _ G): (f.difference f').value X z=f.value X z-f'.value X z:= by unfold difference shrink sumTwo mapSmooth; dsimp only; ring

lemma log_scale (H : Cash W s μ L Q o C T R)(a:ℝ)(p:Molecule S)(V:Config G c)(χ : Chi)(f':Insert T):
   (f'.shrink a).onLog H χ p V=a*f'.onLog H χ p V:= by
   unfold onLog
   have h(X:PhysicalNext.Repeat.Greenbelt.Reserve S):let Z:=PhysicalNext.Repeat.Greenbelt.prism T s χ o.K V (PhysicalNext.Repeat.Greenbelt.allot X); (f'.shrink a).preGauge H p Z=a*f'.preGauge H p Z:=by
     intro Z; unfold preGauge
     have h {F : Forest S.ratio}(X:Coat T F):(f'.shrink a).inTags H p X=a*f'.inTags H p X:=by
        unfold inTags; split
        next=>
          let Y i:= ((preps X (roster p)).taggedL i)
          let v:= podium S G (H.unionP p) (radiusB s)
          have hF i : (f'.shrink a).onSlice v (Y i)=a*f'.onSlice v (Y i):=by
             unfold onSlice shrink mapSmooth; dsimp only; simp_rw [mul_left_comm _ a,integral_const_mul]
          change likely (fun i=> (f'.shrink a).onSlice v (Y i))= a* likely _; simp_rw [hF]
          unfold likely; rw [mul_left_comm a, Finset.mul_sum _ _ (a := a)]
        rw [mul_zero]
     simp_rw [h, integral_const_mul]
   dsimp only at h; simp_rw [h]; unfold likely; rw [mul_left_comm a, Finset.mul_sum _ _ (a := a)]
end Insert

namespace Fits
open Insert
variable {p:Molecule S} {χ : Chi} {f₁ f₂:Insert T}{u : Support c}{Ξ : Captain H j C' d v Y A b q B η k χ}
    (hf : Fits H f₁ u j)(hp:Fits H f₂ u j)
lemma sumTwoEq (g g': Insert T):Insert.sumTwo g g'=Insert.together Finset.univ ![g,g']:=by
   change Insert.mk _=Insert.mk _; congr! 1; funext F X z; simp [Fin.sum_univ_succ]
include hf hp
lemma sumTwo_fits : Fits H (f₁.sumTwo f₂) u j:=by
   rw [sumTwoEq]; apply Fits.together; intro i _; fin_cases i<;> simpa using! ‹Fits ..› 
omit hp in
lemma shrinkFits : Fits H (f₁.shrink r) u j:= hf.mapSmooth (by fun_prop)
lemma diffFits : Fits H (f₁.difference f₂) u j:= sumTwo_fits hf hp.shrinkFits

variable {t : ℝ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x:E} {V:E → Config G c}
include Ξ
omit hp hf
lemma sumTwoGerm (hf:Fits H f₁ (H.unionP p) j)(hp : Fits H f₂ (H.unionP p) j)(he : (roster p).flags=∅) (h : Mode V x j v)(hV : Healthy (Pressure.temp s) (H.unionP p) (V x)):
   (f₁.sumTwo f₂).onLog H χ p ∘ V =ᶠ[𝓝 x] fun y=> f₁.onLog H χ p (V y)+f₂.onLog H χ p (V y):=by
   rw [sumTwoEq]; let f(i:Fin 2):= ![f₁,f₂] i
   have ht(i:Fin 2):Fits H (f i) (H.unionP p) j:=by fin_cases i; exact hf; exact hp
   simpa only [Function.comp_def,f,Fin.sum_univ_succ,Finset.univ_eq_empty,sum_empty,add_zero,cons_val_zero, cons_val_succ] using Fits.sum_onLog (Ξ:=Ξ) he (w:=univ) (fun (i:Fin 2) _=>ht i) h hV -- names

lemma diffGerm (hf:Fits H f₁ (H.unionP p) j)(hp:Fits H f₂ (H.unionP p) j)(he : (roster p).flags=∅) (h : Mode V x j v)(hV : Healthy (Pressure.temp s) (H.unionP p) (V x)):
   (f₁.difference f₂).onLog H χ p ∘ V =ᶠ[𝓝 x] fun y=> f₁.onLog H χ p (V y)-f₂.onLog H χ p (V y) := by
   simpa only [sub_eq_add_neg,Insert.log_scale,Insert.difference,neg_one_mul] using Fits.sumTwoGerm (f₂:=f₂.shrink (-1)) (Ξ:=Ξ) hf hp.shrinkFits he h hV
end Fits

namespace Retain
namespace Telegraph
variable {k:ℕ} {α β A W:ℝ} {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {x:E} {g h:E→ℝ} {t:Type} {f q:t→E→ℝ}{v d:t→ℝ}
-- fundamental absolute telescoping Lemma without assuming f−g lower
-- derivatives commute (analytic already). charge tally.Scalculus BEFORE
-- averaging/support or reducing gradient.Hessian.
lemma fades (S':Finset t)(hf:∀ i∈S', Brush k (v i) (d i) (f i) x)(hh:∀ i∈S', Brush k (v i) (d i) (q i) x)(he:∀ i∈S', Brush k (α*v i) (d i) (fun x=>f i x-q i x) x):
    Brush k (α*S'.card*∏ i∈S',v i) (∑ i∈S',d i) (fun x=>(∏ i∈S',f i x)-∏ i∈S',q i x) x := by
   induction S' using Finset.induction_on with
   | empty=> simp; exact Brush.zi EventuallyEq.rfl le_rfl le_rfl
   | insert i S' hi hp=>
     have H := hp (fun i h=>hf i (Finset.mem_insert_of_mem h)) (fun i h=>hh i (Finset.mem_insert_of_mem h)) (fun i h=>he i (Finset.mem_insert_of_mem h))
     have hp':= Brush.all_prod S' q _ _ (fun i h=>hh i (Finset.mem_insert_of_mem h))
     have hF:= ((hf i (Finset.mem_insert_self ..)).paints H).gathering ((he i (Finset.mem_insert_self ..)).paints hp')
     simp_rw [prod_insert hi, sum_insert hi]; refine hF.shimmy ?_ |>.climb ?_ le_rfl
     · filter_upwards with x; ring
     rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]; apply le_of_eq; ring

lemma strip (n:ℕ) (hG : Brush k A W g x)(hH: Brush k A W h x)(hK: Brush k (α*A) W (fun x=> g x-h x) x):
    Brush k (α*n*A^n) (n*W) (fun x=> g x^n-h x^n) x:= by
   simpa only [prod_const,nsmul_eq_mul,sum_const,Finset.card_range] using! fades (range n) (fun _ _=>hG) (fun _ _=>hH) (fun _ _=>hK)
lemma powers (n:ℕ)(hG: Brush k A W g x) : Brush k (A^n) (n*W) (fun x=> g x^n) x:=by
   simpa only [prod_const,nsmul_eq_mul,sum_const, Finset.card_range] using! Brush.all_prod (range n) (fun _=>g) _ _ (fun _ _=> hG)
end Telegraph
end Retain
end YM.RGLocalTaylor
