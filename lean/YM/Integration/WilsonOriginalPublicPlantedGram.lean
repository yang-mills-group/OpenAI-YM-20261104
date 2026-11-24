import YM.Integration.WilsonOriginalPublicPlantedGramBudget
import YM.Integration.WilsonPositionProgramPublicReflectedRead

/-! Uniform leading Gram of the signed public position columns on the
actual finite directory when the upper index is chosen before the high
Taylor order. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedGram
open Set Finset Filter Metric Function Lattice Maxwell XSpace XSpace.Cirrus XSpace.Structure1
open XSpace.Normalize FVA2 FVA2.Register MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicWickGram
open WilsonPositionProgramPublicDirectoryCoin
open scoped Classical Topology BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z g M T dial){d:ℕ}{I:Type}[Fintype I]{B₀:Local.Physical.Deck G}
    (a:Axis)(legs:I→Glyph B₀ d)(q:ℕ)

def measured {j B:ℕ}(P:Handoff.Directory Z j B)(u:ℝ)(s:Sample 2)(i k:I):ℂ :=
  drawValue Z (signed a legs i k) q P u s.layout

include H in
theorem original (δ:ℝ)(hd:0<δ)(l:Filter ℝ){t:ℝ→ℝ}
    (pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))(D:ℕ)(C:ℝ):
    ∃ j₀:ℕ,∃ ρ:ℝ,0<ρ ∧ ∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
      ∀{B}(P:Handoff.Directory Z j B),Handoff.Directory.budget G 2 d+q≤B →
      ∀s:Sample 2,s.F=Z.run.step j → welcome s → dist (familiar s) (lower a)<ρ →
      ∀u:ℝ,|u|≤8*t r → ‖measured Z a legs q P u s-reading a (nodes a) legs‖≤δ := by
  obtain ⟨b,hb,domain⟩:=Metric.mem_nhds_iff.mp ((conf_open 2).mem_nhds (separated a))
  let K:=closedBall (lower a) (b/2)
  have compact:IsCompact K:=isCompact_closedBall ..
  have sep:K⊆conf 2:=fun _ h=>domain (lt_of_le_of_lt (mem_closedBall.mp h) (by linarith))
  have family (i k:I):=WilsonOriginalPublicPlantedGramBudget.original Z H (signed a legs i k) q
      compact sep l pos small D C (half_pos hd)
  choose date owed using family
  have all:=eventually_all.mpr (fun i=>eventually_all.mpr (fun k=>owed i k))
  obtain ⟨ε,he,fee⟩:=gate_senses (lower a)
      (Metric.tendsto_nhds.mp (earned Z.scheme Z.store a legs) (δ/2) (half_pos hd))
  obtain ⟨j₁,ready⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually fee)
  let j₀:=j₁+∑i,∑k,date i k
  refine ⟨j₀,min (b/2) ε,lt_min (half_pos hb) he,?_⟩
  filter_upwards [all] with r bills j hj short B P cov s hs admitted near u hu
  have jbase:j₁≤j:=le_trans (Nat.le_add_right ..) hj
  have use₁:=ready j jbase s.layout s.center (by simpa only [welcome,←hs] using admitted)
  have hfree:‖matrix Z.scheme Z.store a legs s-reading a (nodes a) legs‖<δ/2:=by
    rcases s with ⟨F,x,c⟩
    dsimp at hs
    subst F
    simpa only [dist_eq_norm] using use₁ (near.trans_le (min_le_right ..))
  have member:familiar s∈K:=mem_closedBall.mpr (near.le.trans (min_le_left ..))
  have budget:‖measured Z a legs q P u s-matrix Z.scheme Z.store a legs s‖≤δ/2:=by
    apply (pi_norm_le_iff_of_nonneg (half_pos hd).le).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (half_pos hd).le).mpr
    intro k
    have smallDate : date i k≤∑i,∑k,date i k :=
      (single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ k)).trans
        (single_le_sum (f:=fun h=>∑k,date h k) (fun _ _=>Nat.zero_le _) (mem_univ i))
    exact bills i k j (smallDate.trans ((Nat.le_add_left ..).trans hj)) short P cov s hs admitted member u hu
  exact (norm_sub_le_norm_sub_add_norm_sub ..).trans (by linarith)

end YM.Integration.WilsonOriginalPublicPlantedGram
