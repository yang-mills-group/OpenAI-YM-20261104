import YM.QuadraticLocal.Fk.Window
import YM.Comparison.RG02.Adjacent.Sale
import YM.Comparison.RG02.Valence.Volume

/-! The two finite marked banks entering measured recalibration have a
common boundary-field degree, fixed before the torus, forest and tests. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Finset Lattice RG Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Precision Exterior Tree Comparison.RG02 Valence Adjacent Analysis
open scoped Classical ContDiff BigOperators

private theorem affine_level {X Y:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (z:Y) (L:X→L[ℝ]Y)
    {n:ℕ} {f:Y→ℂ} (hf:Level (n:ℤ) f) : Level (n:ℤ) (fun x=>f (z+L x)) := by
  induction n generalizing f with
  | zero =>
    have con : (fun x=>f (z+L x)) = fun _=>f 0 := funext fun x=>by
      simpa [Assembly.jet_zero] using hf.posted (z+L x)
    rw [con]; exact Level.constant _
  | succ n ih =>
    apply Level.up (by positivity) (hf.smooth.comp (contDiff_const.add L.contDiff))
    intro v
    have hd : Analysis.D v (fun x=>f (z+L x))=fun x=>Analysis.D (L v) f (z+L x) := by
      funext x
      have der : HasFDerivAt (fun u=>f (z+L u)) ((fderiv ℝ f (z+L x)).comp L) x :=
        (hf.smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp x (L.hasFDerivAt.const_add z)
      exact congrArg (fun T:X→L[ℝ]ℂ=>T v) der.fderiv
    change Level _ (Analysis.D v (fun x=>f (z+L x)))
    rw [hd,show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    apply ih
    convert hf.down (L v) using 1; omega

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {J:Census V}
    {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
    (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors J G f)
    (η:V→ℕ) (v:J.Mode)

/-- Rank needed for this marked mode after normalization and logarithm. -/
def resetDegree (η:V→ℕ) (v:J.Mode) (r:ℕ) := r+2+Launch.index J η v

theorem ledger_charge (hC:∀ l:Hot J, C.power l = Launch.index J η l.val+1) (r:ℕ) :
    Charge r (fun _=>(resetDegree η v r:ℤ)) (fun j z=>
      (Order.observe J r (Order.logMarked (Bulk.Fk K F tag C (Stationary.arm G c 1 z) r)) j).part v) := by
  have h : Toile C.power v (fun i=>(η i:ℤ)) := by
    intro l _
    rw [hC l]; change ((∑ i∈l.sites,η i)+1:ℕ) ≤ (2:ℤ)+∑ i∈l.sites,(η i:ℤ)
    push_cast; omega
  intro j hj
  let A := fun x=>(Order.observe J r (Order.logMarked (Bulk.Fk K F tag C x r)) j).part v
  have hl : Level ((resetDegree η v j:ℕ):ℤ) A := by
    have hb := Valence.mark_read K F tag C (r:=r) (fun i=>(η i:ℤ)) v j h
    simpa [resetDegree,Launch.index,A] using hb
  have ret := affine_level 0 (Stationary.arm G c 1).toContinuousLinearMap hl
  simp only [zero_add] at ret
  apply ret.promote; change (resetDegree η v j:ℤ) ≤ (resetDegree η v r:ℤ); unfold resetDegree; omega

omit [Fintype V] in
theorem painter_charge {c:Side} (C:Bulk.Colors J G c)
    (hC:∀ l:Hot J, C.power l = Launch.index J η l.val+1)
    (hA:∀ l:Hot J, ContDiffAt ℝ ω (Bulk.projected (C.mark l)) 0) (r:ℕ) :
    Charge r (fun _=>(resetDegree η v r:ℤ)) (fun j z=>(Air.discharge C j (Stationary.arm G c 1 z)).part v) := by
  intro j hj
  by_cases empty:v=J.quiet
  · simp_rw [empty,Air.discharge,Multi.part_lit_quiet]; exact Level.zero _
  let l:Hot J:=⟨v,(Cumulants.hot_iff_ne _).2 empty⟩
  let X:=Exterior.fieldDir G c 1
  let L := (ContinuousLinearMap.inr ℝ ℝ X).comp (Stationary.arm G c 1).toContinuousLinearMap
  have rank := affine_level (1,(0:X)) L (Adjacent.levelJet (hA l) (C.power l+j))
  have same : (fun z=>(Air.discharge C j (Stationary.arm G c 1 z)).part v) =
      fun z=>Assembly.jet (Bulk.projected (C.mark l)) (C.power l+j) ((1,(0:X))+L z) := by
    funext z
    rw [show (Air.discharge C j (Stationary.arm G c 1 z)).part v=_ from Multi.part_lit _ l]
    congr 1; ext <;> simp [L]
  change Level (resetDegree η v r:ℤ) (fun z=>(Air.discharge C j (Stationary.arm G c 1 z)).part v)
  rw [same]
  apply rank.promote; rw [hC l]; unfold resetDegree; change ((Launch.index J η v+1+j:ℕ):ℤ)≤((r+2+Launch.index J η v:ℕ):ℤ); omega

end YM.Integration.FVA1Physical.Wilson
