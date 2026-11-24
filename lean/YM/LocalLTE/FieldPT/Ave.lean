import YM.LocalLTE.FieldPT.Myrrh
/-!
 Genome income and curvature ∆(s): within transport readiness at all represented epochs
 use linear prediction PROGRAM before extracting full ratio in $s$ tolerance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j k z M:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
lemma HexTsum {ι:Type} {g:ℝ→ι→ℝ}(h:Hex j g)(he:∀ s∈Weft.clip,Summable (g s)): Hex j (fun s=>∑' i,g s i):=by
    have hs i: Summable (Weft.pick j g i):= by unfold Weft.pick; simp_rw [Finset.sum_fn]; exact summable_sum (fun k _=> (he _ (Weft.probes j k)).mul_left _)
    refine ⟨fun i=>∑' x,Weft.pick j g i x,fun s hv=>?_⟩; simp_rw [h.seen hv,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [Summable.tsum_finsetSum (fun i _=> (hs i).mul_left _)]; simp_rw [tsum_mul_left]
lemma salaryZ {X:Listing G n}{f:ℝ→ℕ→ Pot G n}{V:Tour X z}{p:BudgetPoint} (h:Genome X V p j k κ f C)(ha:Reliable G κ K)(hG:G.Simple)(hH:∀ (o:Site n) (X:Grove o)(i:ℕ), i< z→ Brush 2 H 1 ((X.crook i Chi.canonical κ (G:=G))∘ Grove.soloV) 0)(hh:1≤ H) : let y s:= (X.read (Price.emp (f s))); let t s:= delta (y s); Hex k t ∧ ∀ s∈Weft.clip, |s^2*t s| ≤ C*(DNA.centered (pie j+1) H 2*(z:ℝ)^2):=by
    intro y w; obtain ⟨a,ha',hz⟩:=h.bills; let k':= DNA.centered (pie j+1) H 2 * (z:ℝ)^2; have hc:0 ≤ k':=by unfold k' DNA.centered Scene.scoreBp; positivity
    let T s:= censusAt (y s) 0 axes01 axes01
    have hp i:= DNA.counted hG (hz i) axes01 axes01 ha hh hH
    have he i: Hex k (fun s => T s i) := by
       unfold T censusAt; simp_rw [show ∀ s,(y s).reg=X.reg from fun _=>rfl]; split; exact (hp i).1; exact Hex.constant _
    have hv := (ha' 0)
    let g i:= if (X.reg i).site=0 then p.mass (X.reg i).support (a i) else 0
    have he' s (he:s∈ Weft.clip):SumBudget (fun i=> |s^2*T s i|) (k'*C):= by
         refine budget_mono (budget_scale hc hv) (fun _=>abs_nonneg _) fun i=> ?_; change _ ≤ k'*g i; unfold g; split
         next h=>
           have hT:T s i=projection (X.reg i) (f s i) axes01 axes01:=if_pos h
           rw [hT,mul_comm k']; exact ((hp i).2 s he).trans (mul_le_mul_of_nonneg_right (p.loMass _ _ (hz i|>.sure)) hc)
         next h=> rw [show T s i=0 from if_neg h,mul_zero,mul_zero,abs_zero]
    have hF s (he:s∈Weft.clip) : Summable (T s) := by
         let g i:= s^2*T s i; have hv : Summable g := Summable.of_norm (he' _ he).2.1
         refine (hv.mul_left ((s^2)⁻¹)).congr (?_); intro i; unfold g; rw [inv_mul_cancel_left₀ (pow_ne_zero _ he.1.ne')]
    refine ⟨HexTsum (Hex.invert he) hF,fun i hi=>?_⟩; change |i^2*(∑' j,T i j)|≤ _; rw [← tsum_mul_left]; exact (_root_.norm_tsum_le_tsum_norm (f:=fun j=>i^2*T i j) (he' _ hi).2.1).trans ((he' _ hi).2.2.trans (mul_comm k' _).le) -- edit
end YM.AnalyticBridge.VerifiedReset.Collection.Price
