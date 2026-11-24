import YM.AllOrder.Floe.Setting
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Crest
/-! Choose curvature book through all orders *before* L restriction. Takes peak.T.Purchase implied basis via canon. Keep regulator link unmasked & Symm actions. -/
open WilsonStartup WilsonStartup.Design WilsonStartup.Padded Work Tensor
variable (p:Clip)
open StateE Pace
-- coherent.K.Poses. orientation. costs can be paid at Stage → potion book for power Vs direct.
def ceiling (i:ℕ) : Age:= ⟨i,i+3,le_rfl⟩
def tile (G:Gauge)(i:Age):= if i=ceiling i.grade then place p G i.r else fun _ =>Extra.Iteration.blank G i.r
lemma yes (G:Gauge)(i:ℕ): tile p G (ceiling i)=place p G (i+5):= if_pos rfl
lemma info (G:Gauge)(i:Age)(σ:ℝ): Quoted (tile p G i) σ (allowance p G i.r σ):= by
 have he(k:ℕ)(h:k=2): Extra.Iteration.Silent (ι:=ℕ) (G:=G) (h ▸ fun _=>Extra.Iteration.blank G k):=by subst k; exact blank_silent -- names
 unfold tile; by_cases hi:i=ceiling i.grade; · have hh : i.r=i.grade+5:= congr_arg Age.r hi; rw [if_pos hi]; exact ⟨grant p G i.r σ,moves p G i.r,fun h=>by omega⟩
 rw [if_neg hi]; exact ⟨ Extra.Iteration.Charged.mono (blank_cost _) le_rfl (by unfold allowance Atom.budget Atom.magnitude; exact Finset.sum_nonneg (fun _ _=> by positivity)),fun _=>blank_sym,he _⟩
lemma no_loop (U:Config G n): Precision.loop (Design.top G p) U=0:= by simp [Precision.loop,Patch.average,Design.top,Precision.uncut, extract_unmasked,Tensor.diagonal]
lemma nogo (R:Pace.Scene G)(k:ℕ) (n:Side): factor (0:Pace.Coin) R k n=0:= by rw [weighs]; simp
lemma nostep (R:Pace.Scene G)(k:ℕ) (n:Side): factor (just 1) R k n= R k n:= by rw [weighs,sum_eq_single 0 ?_ (by simp),just,if_pos rfl,one_smul,Nat.sub_zero]; · intro j hj hp; rw [just,if_neg hp,zero_smul]
lemma gone (v:ℝ):Pace.ladder v 0=just 1:= by
 have hf (k:ℕ) : Act k (fun _=> (0:ℝ)) 0:= by rw [show (0:Word ℝ)=just 0 by ext; simp [just]]; exact Act.static _
 funext x; refine (coin_word (k:=x) v (hf _) rfl).trans_at ?_ le_rfl
 simpa only [add_zero,Real.one_rpow] using Act.static (n:=x) (1:ℝ)
lemma gridN (G:Gauge)(i:Age) (n:Side)(k:ℕ):Pace.moiety 0 i (tile p G) k n=jet (turnSeries (tile p G i) (m:=n)) (k+2):= by
 unfold moiety; rw [gone,nostep]; by_cases ht:i=ceiling i.grade; · have hT:i.r=i.e+2:= congr_arg Age.r ht; unfold trade; split; rw [show k-i.e+i.r=k+2 by omega]; rename_i he; ext1 x; have hh:= info p G i 1; have h:= hh.pay; symm; rw [jet,(rays_jet (turns_analytic (tile p G i) zero_lt_one h) i.r).1 (turns_low _ zero_lt_one h) (k+2) (by omega)]; simp
 have hx : turnSeries (tile p G i) (m:=n)=0:= by ext x; simp [tile,ht,turnSeries,Patch.average, Precision.uncut,Atom.unmasked,Extra.Iteration.blank,Atom.poly]
 unfold trade; split <;> rw [hx] <;> ext x <;> simp [jet]
lemma gridV(n:Side)(U:Config G n)(A:ℝ)(i:Age): sketch (tile p G) i n A U=Extra.Iteration.action (tile p G i) U:= by
 unfold sketch; by_cases ht:i=ceiling i.grade; · have hT:i.r=i.e+2:= congr_arg Age.r ht; rw [show i.stamp=0 by unfold Age.stamp; rw [hT,Nat.sub_self]]; simp
 change A^i.stamp * _ =_; simp [tile,ht,Extra.Iteration.action,Patch.average,Precision.uncut,Atom.unmasked,Extra.Iteration.blank,Atom.poly]
open Step
lemma formgrid {E:Type} [AddCommMonoid E] (m:ℕ)(f:Age→E)(h:∀ i,i≠ceiling i.grade→f i=0): ∑ i∈Age.scope (m+2),f i=∑ j∈ range m,f (ceiling j):= by induction m with
 | zero=>simp only [show Age.scope (0+2)=_ from coke,sum_empty,range_zero]
 | succ m ih=> rw [show Age.scope (m+1+2)=upto m∪ Age.scope (m+2) from (revealed m).symm,Finset.sum_union (fresh_set m),sum_range_succ, ih, add_comm, sum_eq_single (s:=upto m) (ceiling m) ?_ (by simp [((tier (ceiling m)).mpr (show (ceiling m).grade=m from rfl))])]; intro i hi hp; apply h; rw [(tier i).mp hi]; exact hp
abbrev scene (p:Clip)(m:ℕ)(U:Config G n):=∑ i∈Age.scope (m+2),Extra.Iteration.action (tile p G i) U
lemma site (m:ℕ)(U:Config G n): scene p m U= bulk p *∑ b: WilsonStartup.Cell n, fill m (faceValue U b):= by
 have he(i:ℕ):Extra.Iteration.action (tile p G (ceiling i)) U=_:= (show Extra.Iteration.action (tile p G _) U= Extra.Iteration.action (place p G (i+5)) U from congr_arg (fun G=>Extra.Iteration.action G U) (yes p G i))
 rw [scene,formgrid]; simp_rw [he,Crest.read]; rw [sum_comm]; simp_rw [← mul_sum]
 intro i hi; simp [tile,hi,Extra.Iteration.action,Patch.average, Precision.uncut,Atom.unmasked,Extra.Iteration.blank,Atom.poly]
end Crest
end YM.AllOrder.Floe
