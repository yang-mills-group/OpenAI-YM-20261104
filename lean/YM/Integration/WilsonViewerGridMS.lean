import YM.Integration.WilsonViewerGridTests

/-! The actual separately ruled finite Wilson-coefficient experiment at a
real continuum argument, with the regulator's own box, grid and finite field solve. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerGridMS
open Filter Set Function Finset MeasureTheory Spec PhysMS
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Book.Program MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionProgramFixedFrame
open WilsonPositionSeparatedProfileMatching WilsonViewerElectedHierarchy
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} (Z:WilsonPrescription G) {simple:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)
    (ν:ℝ) {d n:ℕ} (v:Fin n → Sec G d)

def directory (i n d q:ℕ):Handoff.Directory Z i (Handoff.Directory.budget G n d+q):=
  Classical.choice (ms.packets i _)

def read (q:ℕ) (t:ℝ) (y:Points n) (i:ℕ):ℂ :=
  ∑ k∈range (q+1), t^k • value Z (M:=M) ν v k (fun z j=>WilsonPositionProgramPoint.entry Z (T:=σ)
    (directory Z M ms i n d q) d ν (draw y (Z.run.step i) (river (Z.run.step i))) (Dframe.fill z) j)

include ms in
private theorem mesh :
    Tendsto (fun i=>Speed.chip (Z.run.step i)+(Z.run.step i).spacing) atTop (𝓝 0) := by
  have ht:Tendsto (fun i=>(Z.run.step i).spacing) atTop (𝓝 0):=frontier.endpt.comp ms.onSchedule
  have u:ContinuousAt (fun z:ℝ=>z^Tide.mildG) 0:=
    Real.continuousAt_rpow_const _ _ (Or.inr Tide.mild_p.le)
  simpa only [Speed.chip,Function.comp_apply,Real.zero_rpow Tide.mild_p.ne',zero_add]
    using (u.tendsto.comp ht).add ht

/-- Each finite register in the same copy gives its full MS reading at the
point on its own normalized regulator band. -/
theorem point (q:ℕ) (t:ℝ) (y:Points n) (clear:y∈conf n) :
    Tendsto (read Z M ms ν v q t y) atTop (𝓝 (approximate (coefficient Z M ν d v) q t y)) := by
  have entered (k:ℕ)(price:k≤q) : Tendsto (fun i=>value Z (M:=M) ν v k (fun z j=>
      WilsonPositionProgramPoint.entry Z (T:=σ) (directory Z M ms i n d q)
        d ν (draw y (Z.run.step i) (river (Z.run.step i))) (Dframe.fill z) j)) atTop
      (𝓝 (coefficient Z M ν d v k y)) := by
    have id:coefficient Z M ν d v k y=Measure.outlook Z.scheme Z.criterion d n ⟨y,clear⟩ k v:=by
      simp only [WilsonViewerElectedHierarchy.coefficient,extended,dif_pos clear]
      exact WilsonPositionHomogeneousComparison.filed Z M ms ν d ⟨y,clear⟩ v k
    rw [id]
    obtain ⟨B,_,prices⟩:=auxiliary Z ms ν v k {y} isCompact_singleton (singleton_subset_iff.mpr clear)
    have small:Tendsto (fun i=>B*(Speed.chip (Z.run.step i)+(Z.run.step i).spacing)) atTop (𝓝 0):=by
      simpa using (mesh Z M ms).const_mul B
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (prices.mono fun i ready=>
      ready _ (directory Z M ms i n d q) (by omega) _ (mem_singleton y)) small
  unfold read approximate WilsonThermometerWeakCoefficientTail.part
  exact tendsto_finsetSum _ fun k hk=>(entered k (Nat.le_of_lt_succ (mem_range.mp hk))).const_smul _

end YM.Integration.WilsonViewerGridMS
end
