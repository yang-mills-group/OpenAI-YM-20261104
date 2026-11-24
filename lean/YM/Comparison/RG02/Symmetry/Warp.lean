import YM.Comparison.RG02.Symmetry.Rise
/-! # Power-basis Ward identity, with thermal pad in log at order zero
    Warps along any allowed curves (announced finite order; every periodic gauge generator
    moving `x` through a `Flow`). Includes own lower-order terms under changes of scale/gauge.
    No magnitude savings. Includes only bulk branch. No projection in period or lifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Valence Ribbon
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (w : S.Choices)
  (a b : ℝ→fieldDir G c 1)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (W : Bulk.Colors R G f) (r : ℕ)
local notation "φ"=> 𝓝 (0:ℝ)
local notation "Ω" x=> Bulk.Fk K F w W x r
local notation "κ"=> pad K F w 0
local notation "ν"=> fuse R r
local notation "X"=> fieldDir G c 1
open YM.Extra.Trajectories (connected)

namespace Orbit
local notation "E"=> Board R r
local notation "P0"=> price K F w
def expCost := fun v:ℝ=> Real.exp (((P0 (a v))-(P0 (a 0))).re)
def grade : Grade R r:= ν (raw K F w a W r)
def tissue : Grade R r:= spring R r (fun t=> (↑(expCost K F w a t):ℂ))
lemma tissue_mono : UnitLeading (tissue (R:=R) K F w a r) := by unfold UnitLeading tissue; rw [stamped]; simp [expCost]
lemma grade_mono : UnitLeading (grade K F w a W r) := fuse_leading (leads_raw K F w a W r)
local notation "sκ" y => (tissue (R:=R) K F w y r)
local notation "s" x => (grade K F w x W r)
local notation "u" x => (pulse K F w x)
variable (ha : glows a)
include ha
lemma ledgerRoot : Ready r (raw K F w a W r) (grade K F w a W r) := ⟨⟨seen_raw K F w a W r ha, ready_raw K F w a W r,rfl⟩, leads_raw K F w a W r⟩
private def flowCost (t:ℝ) := (P0 (a t)).re-(P0 (a 0)).re
private lemma pays : ContDiffAt ℝ ω (flowCost K F w a) 0 := (((Complex.reCLM.contDiff.comp (price_ready K F w)).contDiffAt).comp _ ha).sub contDiffAt_const
private lemma comeDown : spring R r (P0 ∘ a)= logVac (sκ a) + (P0 (a 0) • 1):= by
    let L := flowCost K F w a; have h:L 0=0:= sub_self _
    have he:= pays K F w a ha; rw [tissue,show expCost K F w a=fun x=> Real.exp (L x) from rfl, logWallet R r he h, ← scale_retain R r (P0 (a 0))]
    have ht : P0 ∘ a = (fun x=> (↑(L x):ℂ)) +fun _=>P0 (a 0):= by funext t; simp [price, Function.comp_apply,L,flowCost]
    rw [ht,denominations]; exacts [(Complex.ofRealCLM.contDiff.contDiffAt.comp _ he),contDiffAt_const]
-- move: lit kernel scale compensation includes pad; mark unaffected by this scalar.
lemma capital : ν (Symmetry.lit K F w a W r)= ((u a) 0) • ((sκ a)*(s a)):= by
    let B (t:ℝ): ℂ:= ↑(expCost K F w a t); let z:= raw K F w a W r
    let f:ℝ→Grade R r:= heat R r B*z
    have hB := heat_seen R r B (by exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (pays K F w a ha).exp)
    have hz := seen_raw K F w a W r ha
    have ht : Symmetry.lit K F w a W r= pulse K F w a 0 • (heat R r B*z):= by
        funext t
        unfold Symmetry.lit; change pulse K F w a t • z t = pulse K F w a 0 • ( (B t • 1) * z t)
        rw [smul_mul_assoc,one_mul,smul_smul, pulse, tax K F w (a t) (a 0), Complex.ofReal_mul,mul_comm (↑_:ℂ)]; rfl
    rw [ht,fuse_scale (hB.product hz),fuse_prod hB hz]; rfl

local notation "Γ" x => grade K F w x W r
variable (hb : glows b) (hk:Bulk.Well W) (h : Flow a b)
include D hb h hk r
lemma arrives : pulse K F w a 0=pulse K F w b 0 := by rw [← stamp_lit K F w a W r, balances K D F w a b W r hk ha hb h, stamp_lit]
private lemma books : (sκ a)*(s a)=(sκ b)*(s b) := by
   have ht:= balances K D F w a b W r hk ha hb h; rw [capital K F w a W r ha,capital K F w b W r hb,arrives K D F w a b W r ha hb hk h] at ht
   exact (smul_right_inj (show (u b) 0≠0 from Complex.ofReal_ne_zero.mpr (pad_pos ..|>.ne'))).mp ht
private lemma pausing : P0 (a 0)=P0 (b 0) := by
   have hh:= Complex.ofReal_inj.mp (arrives K D F w a b W r ha hb hk h); have ht:= tax K F w (a 0) (b 0); change _=κ (b 0) at hh; rw [hh] at ht
   have he: Real.exp (P0 (a 0) - P0 (b 0)).re=1:= mul_right_cancel₀ (pad_pos K F w 0 _|>.ne') (by rw [← ht,one_mul])
   exact Complex.ext (sub_eq_zero.mp (Real.exp_injective (he.trans Real.exp_zero.symm))) (by simp [price])
omit ha hb D h hk in
private lemma climb₁ (x:ℝ→X) : logVac ((sκ x)*(s x))=logVac (sκ x)+ logVac (s x):= by unfold logVac denominator; rw [map_mul]; exact Cumulants.connected_mul ( (bottom_quiet ..).trans (tissue_mono ..)) ((bottom_quiet ..).trans (grade_mono ..))
omit D h hk ha hb in
private lemma climb₂ (x:ℝ→X) : Order.ratio ((sκ x)*(s x))=Order.ratio (s x):= by
    have hx: UnitLeading ((sκ x)*(s x)):=by rw [UnitLeading,Poly.quiet_mul, tissue_mono,grade_mono]; exact mul_one _
    symm; apply Order.ratio_unique hx; unfold denominator; rw [map_mul,show bottom _ _ (sκ x)=sκ x from sprouted ..,mul_assoc,show bottom R r (s x)*Order.ratio (s x)=s x from recovers (grade_mono ..)]
lemma vacuum_log : spring R r (P0 ∘ a)+logVac (s a)=spring R r (P0 ∘ b)+logVac (s b):= by
    have he := pausing K D F w a b W r ha hb hk h
    rw [comeDown K F w a r ha,comeDown K F w b r hb,he]
    rw [add_right_comm,add_right_comm _ (_ • _), ← climb₁ K F w W r a, ← climb₁ K F w W r b,books K D F w a b W r ha hb hk h]
lemma mark_m : Order.ratio (Γ a)=Order.ratio (Γ b) := by rw [← climb₂ K F w W r a,← climb₂ K F w W r b,books K D F w a b W r ha hb hk h]
lemma mark_log : logMarked (Γ a)=logMarked (Γ b):= congrArg connected (mark_m K D F w a b W r ha hb hk h)
end Orbit
end YM.Comparison.RG02.Symmetry
