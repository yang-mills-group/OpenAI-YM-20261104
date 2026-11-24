import YM.Comparison.RG02.Symmetry.Warp
/-!
# Warped root negotiation and lowest remaining unmatched order

State the `Sheet`: includes its own lower order terms in a path Ward derivative statement
in **same** fine-unit external parameter charts and normalization. Includes canon thermal pay
(at order zero); no upper reset implicitly made. Projection of log vacuum therefore through the
full gauge-aware recalibration. Use on analytic/cut regulator series only when this Warp is
realized, not asserted for any future iteration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry.Orbit
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Valence Ribbon
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (w : S.Choices)
  (a b : ℝ→fieldDir G c 1)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (W : Bulk.Colors R G f) (r : ℕ) (s : R.Mode)
local notation "Ω" x => Bulk.Fk K F w W x r
local notation "P0"=> price K F w
local notation "X"=> fieldDir G c 1
local notation "Γ" x=> grade K F w x W r

def ground (n:ℕ) (x:X) := detail (logVac (Ω x)) R.quiet n + if n=0 then P0 x else 0
def words (n:ℕ) (x:X) := detail (logMarked (Ω x)) s n

def patrol (r:ℕ) (p:ℕ→X→ℂ) (x:ℝ→fieldDir G c 1) := ∑ i∈range (r+1), motion (p (r-i) ∘ x) i
structure Sheet (r:ℕ) (p:ℕ→X→ℂ):Prop where
 known n : n ≤ r → ContDiff ℝ ω (p n)
 follows : ∀ x y : ℝ→fieldDir G c 1, Flow x y → glows x → glows y → ∀ i≤r, patrol i p x=patrol i p y
variable (ha : glows a)
private lemma pay (f:ℝ→ℂ) (he : smooth f) (i:ℕ) (hi : i≤r) : detail (spring R r f) R.quiet i=motion f i:= by
   have hp (t:ℝ): (value (t:ℂ) (heat R r f t)).part R.quiet=f t := by
      unfold heat; rw [show value (t:ℂ) (f t • _) = f t • value (t:ℂ) (1:Grade R r) from (valueL R r ↑t).map_smul _ _,Poly.part_smul];
      have hx : render (1:Grade R r)=(1:Truncated R) := by
         rw [show (1:Grade R r)=series R r (1:PTable R) from (map_one (series R r)).symm, series_render]; exact PowerSeries.trunc_one (R:=Poly R) r
      rw [value_render, hx, map_one]; simp
   rw [spring, ← valued (heat_seen R r f he) (Eventually.of_forall (heat_save R r f)) hi,_root_.funext hp]
private lemma remit (u v: Grade R r) (t:R.Mode) (i:ℕ): detail (u+v) t i=detail u t i+detail v t i:= by unfold detail; rw [observe_add,Poly.part_plus]
include ha
lemma pwords (i:ℕ)(h:i≤r) : detail (logMarked (Γ a)) s i= patrol i (words K F w W r s) a := (ledgerRoot K F w a W r ha).turnRatio.over.concentrate s i h
lemma pground (i:ℕ) (h:i≤r) : detail (spring R r (P0 ∘ a)+logVac (Γ a)) R.quiet i=patrol i (ground K F w W r) a := by
    rw [remit,pay r  _ ( (price_ready K F w).contDiffAt.comp _ (ha)) i h]
    have he:= (ledgerRoot K F w a W r ha).vacant.over.concentrate R.quiet i h; change detail (logVac (Γ a)) R.quiet i=_ at he
    let b k x:= detail (logVac (Ω x)) R.quiet k
    have hm (k:ℕ): ContDiffAt ℝ ω (b k ∘ a) 0:= (vacuum_read K F w W r k).smooth.contDiffAt.comp (f:=a) 0 ha
    rw [he,patrol]; change motion (P0 ∘ a) i+(∑ k∈range (i+1),motion (b (i-k) ∘ a) k)=_
    have hh (k:ℕ)(hk:k∈range (i+1)): motion (ground K F w W r (i-k) ∘ a) k=(if k=i then motion (P0∘a) i else 0)+motion (b (i-k) ∘ a) k := by
       simp_rw [Function.comp_def,ground]; split_ifs with ha' hy hx
       next=> rw [← hy]; exact Eq.trans (Moving.Shift.madd (hm _) ((price_ready K F w).contDiffAt.comp _ ha)) (add_comm ..)
       next=> simp only [mem_range] at hk; omega
       next=> omega
       simp only [add_zero,zero_add]; rfl
    rw [sum_congr rfl hh,sum_add_distrib,sum_ite_eq',if_pos (mem_range_succ_iff.mpr (le_refl i))]
variable (hW : Bulk.Well W)
omit ha
include D hW
lemma colored : Sheet r (words K F w W r s):= ⟨fun i _=> (mark_read K F w W _ s i (every W.power s)).smooth,
   fun x y H h he i hi=> ((pwords K F w x W r s h i hi).symm.trans ((congrArg (fun v=> detail v s i) (mark_log K D F w x y W r h he hW H)).trans (pwords K F w y W r s he i hi)))⟩
lemma bed : Sheet r (ground K F w W r):= by
   refine ⟨fun i _=> ( (vacuum_read K F w W r i).smooth).add ?_,fun x y H h he i hi=>?_⟩
   · change ContDiff ℝ ω (fun x : X=> if i=0 then P0 x else 0); split <;> first | exact price_ready .. | exact contDiff_const
   rw [← pground _ _ _ _ _ _ h i hi, ← pground _ _ _ _ _ _ he i hi,vacuum_log K D F w x y W r h he hW H]

omit D hW
lemma smooth_ground (k:ℕ) : ContDiff ℝ ω (ground K F w W r k):= by
   unfold ground; apply (vacuum_read K F w W r k).smooth.add; split; · exact price_ready ..
   exact contDiff_const
-- reusable displacement at the order with earlier components matched
variable {H J:ℕ→fieldDir G c 1→ℂ} {a b r}
lemma Sheet.unmatched (h : Sheet r H) (hx : Sheet r J) (ha : glows a) (hb : glows b) (hp : Flow a b)
    {k} (ht : k≤r) (hj : ∀ i<k,H i=J i): H k (a 0)-J k (a 0)=H k (b 0)-J k (b 0) := by
   have ht (a:ℝ→fieldDir G c 1): patrol k H a - patrol k J a= H k (a 0)-J k (a 0) := by
      unfold patrol; rw [← sum_sub_distrib,sum_eq_single 0,Nat.sub_zero, Moving.Shift.mzero,Moving.Shift.mzero]; rfl
      · intro i hi he; rw [hj _ (by simp only [mem_range] at hi; omega), sub_self]
      simp
   rw [← ht a, ← ht b,h.follows a b hp ha hb k (by assumption),hx.follows a b hp ha hb k (by assumption)]
end YM.Comparison.RG02.Symmetry.Orbit
