import YM.LocalLTE.Pool.Trays
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
variable (hs : Reliable G κ k) (hG:G.Simple)(hn:20<n.val) (hb:Decent c p)
lemma paused (i:Key n)(Y:Support n)(U:Config G n) : ∑ j: Fin (M+2), masked p.threshold Y (rota G i j.val M κ) U=masked p.threshold Y i.accrual U:=by
    rw [Fin.sum_univ_eq_sum_range (fun j=> masked p.threshold Y (rota G i j M κ) U)]
    by_cases h:Healthy p.threshold Y U
    · simp_rw [masked_eq _ _ _ _ h]; rw [Finset.sum_range_succ,rota,if_pos rfl]; rw [Finset.sum_congr rfl (g:=fun j=> if j=0 then Frost.draft G i κ 0 U else Frost.draft G i κ j U- Frost.draft G i κ (j-1) U) (fun j hj=> by have hx:= Finset.mem_range.mp hj; unfold rota; rw [if_neg (by omega)]; split <;> rfl), show ∑ j∈ Finset.range (M+1), _=_ from Price.bridged (fun j=> Frost.draft G i κ j U) M]; rw [Pi.sub_apply]; ring
    simp_rw [masked_ne _ _ _ _ h]; simp
lemma pausing (U:Config G n)(x κ:ℝ) (i:Key n): ∑ j:Fin (M+2), masked p.threshold (neighbors 4 i.native) (part G M c x κ (j,i)) U= Start.weight c x*masked p.threshold (neighbors 4 i.native) i.accrual U:=by
    let Y:= neighbors 4 i.native; have ht j: masked p.threshold Y (part G M c x κ (j,i)) U= Start.weight c x* masked p.threshold Y (rota G i j.val M κ) U:=by by_cases h:Healthy p.threshold Y U; rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ h]; rfl; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero] -- `;` focus
    change ∑ j:Fin (M+2), masked _ Y _ _=_; simp_rw [ht]; rw [← Finset.mul_sum, paused]
lemma valley (U : Config G n)(x κ:ℝ) : ∑' i,(Frost.iceCap G M p c x κ).logarithm i U=Start.weight c x*∑ i: Key n,Frost.maskH G p i U:=by
    rw [Finset.mul_sum]; apply Padded.totals; intro i; dsimp only [iceCap]; split <;> rfl
lemma engine (U:Config G n)(x κ:ℝ) : ((bank n G M).pours (iceCap G M p c x κ)).additive p U= Start.weight c x*∑ i:Key n,masked p.threshold (neighbors 4 i.native) i.accrual U:=by
    unfold Activities.additive; let T (i:Card M n):= masked p.threshold (neighbors 4 i.2.native) (part G M c x κ i) U
    rw [Padded.totals (α:=Card M n) (g:=T) (fun i=>?_)]
    · rw [Fintype.sum_prod_type,Finset.sum_comm,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> Frost.pausing ..
    simp only [Activities.regularOccurrence,pours,reggo]; split; exact rfl; exact Start.masked_zero _ _ _
lemma cup (U: Config G n) : (trunk (Design.top G c) c p W P x 0).eval U * Real.exp (∑' i,(P).logarithm i U)=(trunk (Design.top G c) c p (dictionary G n) (Start.payload c p G n x) x 0).eval U:=by
    let V:=trunk (Design.top G c) c p W P x 0; let V':= trunk (Design.top G c) c p (dictionary G n) (Start.payload c p G n x) x 0
    have hu: Real.exp (V.exponent U)*Real.exp (∑' i,(P).logarithm i U)=Real.exp (V'.exponent U):=by
        rw [← Real.exp_add, Frost.valley]; unfold Rep.exponent; change Real.exp (_-((bank n G M).pours _).additive p _+_)=Real.exp (_-(Start.raw G n c p x).additive p _); rw [Frost.engine, Start.written_sum]; unfold maskH; simp only [Pi.sub_apply,Finset.sum_sub_distrib]; congr 1; dsimp only [V,V',Progress.DirectedRecipe.trunk]; ring_nf
    unfold RG.Rep.eval; change Real.exp (V.exponent U)*V.activities.gas V.p U*Real.exp _=_; rw [mul_right_comm,hu]; rfl
lemma eats (U:Config G n)(hb:Decent c p): (trunk (Design.top G c) c p W P x 0).eval U * Real.exp (∑' i,(P).logarithm i U)=Wilson.bare x U:= (cup G M p c U).trans (Start.evaluates hb U)
end YM.WilsonStartup.Frost
