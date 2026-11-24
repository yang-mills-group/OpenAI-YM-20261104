import YM.LocalLTE.FieldPT.Paid
import YM.LocalLTE.Estate.Call
/-!
 Preserve full Activities including Moves. Unmask E tolerance from layers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n L : Side} {j z k m i M:ℕ} {W κ K U C V t H u v ε: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene Song Ovens Rack
variable (X:Listing G n)(p:BudgetPoint)(R:PathData G)
open PhysicalNext.Repeat.Mallow
local notation "R'"=> operas X p R M
lemma alphaProject (U:Activities G n) (f: Fin (M+2) × EKey n→ Pot G n) (F G':ℕ→ EKey n → Pot G n) (hp:G.Simple)(hn:20<n.val) (ht:U.E=stuff (Rack.upE (Price.bells p R X M)) (Song.choir f ∘ numbering (Price.Rol M n)))(hL: (charged U (R' F)).Valid p W κ)(hh: (charged U (U.E-(R' F))).Valid p K κ)(h₂:∀ i≤ M,∀ t:EKey n,Comic G (Price.tubeX R p X t) p (F i t))(h₃:∀ i≤ M,∀ t:EKey n, Comic G (Price.tubeX R p X t) p (G' i t))(hK:∀ i≤ M,Stocked p (Price.tubeX R p X) (F i-G' i) v) (hz:U.reg=(drawer G n).reg)(hQ:∀ i j,Nonempty (U.Moves i j)) (hc:0 ≤ v) : let δ:=(M+2:ℕ)*(turnFee p*(2*v)); (charged U (R' G')).Valid p (W+δ) κ∧ (charged U (U.E-R' G')).Valid p (K+δ) κ:=by
   intro δ; let P:= R' F; let T' := R' G'; let V:= charged U P; let W':= charged U (U.E-P); let A:= charged U T'; let B:= charged U (U.E-T');
   have hK (E:ℕ→Pot G n): (charged U E).ForcedFamily p ∧ (charged U E).KBound p κ := by
       obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:= hL.forced; exact ⟨⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩,hL.boundK⟩ -- edit Kbound
   obtain ⟨hs,a,h,hA⟩:= Price.upper X p R M F G' hp hn v h₂ h₃ (by assumption) hc
   have hv (i:ℕ): Comic G (U.reg i) p (B.E i):=by
       have ht:Comic G (U.reg i) p (W'.E i) := ⟨hh.regular.smooth i,hh.regular.at_flat i,hh.regular.vanish i⟩
       have hu:B.E i= W'.E i -( (-1:ℝ) • (P i - T' i)):=by
          rw [neg_one_smul]; change (U.E i-T' i)= (U.E i - P i) - -(P i-T' i); abel
       rw [hu]; exact ht.pair (Comic.scales _ ((hz.symm ▸ (hs i).1).pair (hz.symm ▸ (hs i).2)))
   have hx(i:ℕ):Comic G (U.reg i) p (A.E i):=by rw [hz]; exact (hs i).2
   have hΩ (i j): Nonempty (A.Moves i j)∧ Nonempty (B.Moves i j):= by
       obtain ⟨q,hf,hQ⟩:= Price.gyros X p R M U hz f F G' i j ht (hQ i j)
       refine ⟨⟨⟨q.ep,q.kp,q.reg_site,q.reg_support,q.forced_support,q.forced_inventory,q.forced_tests, fun i a=> congr_fun (hQ _) a,q.valuesK⟩⟩,⟨⟨q.ep,q.kp,q.reg_site,q.reg_support,q.forced_support,q.forced_inventory,q.forced_tests, fun i a=> congr_arg₂ (fun x y:ℝ=>x-y) (q.valuesE i a) (congr_fun (hQ i) a),q.valuesK⟩⟩⟩
   refine ⟨⟨⟨fun i=> (hx i).1,fun i=>(hx i).2.1,fun i=> (hx i).2.2⟩,(hK _).1,fun s t=> (hΩ s t).1,?_,(hK _).2 ⟩,⟨⟨fun i=> (hv i).1,fun i=> (hv i).2.1,fun i=> (hv i).2.2⟩,(hK _).1,fun s t=>(hΩ s t).2,?_,(hK _).2⟩⟩
   · obtain ⟨g,hg,hG'⟩:= hL.boundE; refine ⟨fun i=> g i+a i,fun i=>?_,fun i=>?_⟩ -- via sub pair
     · change p.supBounds _ _ (T' i) _; rw [show T' i=P i-(P i-T' i) from (by abel)]; exact sup_sub (hL.regular.smooth i) (reg_sub (hL.regular.smooth i) (hx i|>.1)) (hg i) (hz.symm ▸ (h i))
     have hv:anchored p U.reg a δ:= hz.symm ▸ hA
     convert budget_plus (hG' i) (hv i) using 2 with j; simp only [charged]; split <;> simp [BudgetPoint.mass, mul_add]
   obtain ⟨g,hg,hG'⟩:= hh.boundE; refine ⟨fun i=> g i+a i,fun i=>?_,fun i=>?_⟩
   · change p.supBounds _ _ (U.E i-T' i) _; rw [show U.E i-T' i=(U.E i-P i)-(-1:ℝ) • (P i-T' i) from (by rw [neg_one_smul]; abel)];
     let E:=P i-T' i; have ht': p.Regular ((U.reg i).support) E:=reg_sub (hL.regular.smooth i) (hx i|>.1); refine sup_sub (hh.regular.smooth i) (AnalyticBridge.CouplingShape.reg_scale (-1) ht') (hg i) ?_; have hk := AnalyticBridge.CouplingShape.sup_scale (-1) (p:=p) (o:=(U.reg i).site) (X:=(U.reg i).support) (f:=E) (show p.supBounds _ _ _ (a i) from hz.symm ▸ h i); rw [abs_neg,abs_one,one_mul] at hk; exact hk
   have hv:anchored p U.reg a δ:= hz.symm ▸ hA; convert budget_plus (hG' i) (hv i) using 2 with j; simp only [charged]; split <;> simp [BudgetPoint.mass,mul_add]
end YM.AnalyticBridge.VerifiedReset.Collection.Price
