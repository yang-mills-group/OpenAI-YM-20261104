import YM.AllOrder.Floe.Frost
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Aero Pace
local notation "Y"=> Link G j
variable (p:Clip)(R:PathData G)(α:ℝ)(L:Layout G)(h:R.Bounds p a C Λ)(hG:G.Simple)
def sloping (α:ℝ)(k:ℕ):ℝ:= if k=2 then α else 0
lemma signature: Earn (sloping α) α := by simp [Earn,sloping]
lemma coke : Age.scope 2=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun i hi=> by have h:= Age.in_scope.mp hi; have h₀:= i.senior; omega
local notation "W"=> Stipend p R α
local notation "F"=> grouping (sloping α) L (Age.scope 2) p R
include h hG
lemma lamps (hk:k≤2): Constant (Stipend p R α k j-F k j):= by
 let f:= inputSeries p R (m:=j); let g:=turnSeries R.loop (m:=j); let r:=intended p R (m:=j); let s:= Coat.summer p R α j
 have hf := stain_knit (m:=j) R p h; have hg:= turns_analytic (m:=j) _ h.width h.two; let v:=α • f+g; have hv:s ∘ input G j=v:= rfl; let V :Y→ℝ:= jet f k
 have hh : W k j - F k j= α • V-Pace.factor (sloping α) (Pace.base p R) k j:= by
    let v':=jet r (k+2); let g':=jet g k
    unfold grouping glory; rw [coke, sum_empty,add_zero]; change v'+jet v k -(v'+g'+ _) =_; ext1 x;
    have hT : jet v k x= α *V x+ g' x:= by rw [show v= _ from (rfl : v=α • f+g),jet_add (show ContDiffAt ℝ ω (α • f) 0 from contDiffAt_const.mul hf.analytic.contDiffAt) hg.contDiffAt]; unfold V g' jet; rw [iteratedFDeriv_const_smul_apply (hf.analytic.contDiffAt)]; simp; unfold f g; ring
    simp_rw [Pi.sub_apply,Pi.add_apply, hT]; change _=α*V x-_; abel
 rw [hh]; by_cases hi:k=2;
 swap
 · have hb: Pace.factor (sloping α) (Pace.base p R) k j=0:=by rw [weighs]; refine Finset.sum_eq_zero fun i hi'=> ?_; rw [sloping,if_neg (by have hv:=mem_range.mp hi'; omega),zero_smul]
   rw [hb,sub_zero]; intro u v; apply congr_arg (α*·); unfold V; have hv':k≤1:= (by omega); interval_cases k
   · simp only [jet_zero]
   unfold jet; rw [show iteratedFDeriv ℝ 1 f 0=0 from Haiku.Project.still_one hG hf.stained hf.analytic]; simp

 subst k; have he:= headTwo p R h (n:=j); rw [weighs,sum_eq_single 2,sloping, if_pos rfl,Nat.sub_self,show Pace.base p R 0 j= _ from he, sub_self]; exact fun x y=>rfl; intro k _ hk; rw [sloping,if_neg hk,zero_smul]; simp
variable {σ:Fees} {T:Age→ι→ℝ} (H: Snap ι G) {V:ι→Scene G}{p}{R:ι→ PathData G}{L:ι→Layout G}{E A0 :ι→ℝ} (F':∀ i,(R i).Bounds p a C (E i)) (s:Age→ℕ)(Γ:ι→ℝ) -- alias price
omit h
include F'
lemma practice (h : Haiku.Coat.strict (fun i k (n:Side)=> V i k n+Stipend p (R i) (A0 i) k n) 3) : Sustained Γ s A0 N σ V R T 0 p L (sloping ∘ A0) := by
 constructor
 · rw [show 0+2=2 from rfl,coke]; exact fun i hi=> False.elim (Finset.notMem_empty i hi)
 · omega
 · exact fun i=> signature _
 · intro i k hk; change sloping _ k=0; exact if_neg (by omega)
 intro i n k hk x y; have he:=h i n k hk x y; have hh:=lamps p (R i) (A0 i) (L i) (F' i) hG (j:=n) (by omega : k≤2) x y; unfold ask; let f:= V i k n; let v:= grouping (sloping (A0 i)) (L i) (Age.scope 2) p (R i) k n; change 0 -f x-v x=0-f y-v y; simp only [Pi.add_apply] at he; simp only [Pi.sub_apply] at hh; unfold f v; linarith only [he,hh]
end YM.AllOrder.Floe.Step
