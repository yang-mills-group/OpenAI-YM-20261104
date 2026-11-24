import YM.Integration.WilsonOriginalPublicFigurePeriod

/-! The normalized response to a measured source opened at its actual fixed
sites on the finite independent vacuum, compared to the same nominated words
on the separately chosen inversion period. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicFigureRate
open Exterior Wilson Tree RegulatorIR.Binding Function Filter Finset Set Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open RegulatorIR.Diagram.Formal RegulatorIR.FVAAlt2.Kick Next.Foundations
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSubmittedGeometry WilsonPositionProgramVariableCircuit
open WilsonOriginalPublicFigurePeriod (shifted stopped source)
open scoped Classical Topology ENNReal BigOperators PowerSeries
variable {G:Gauge}(C:Run G)(D:XSpace.Run){X:Type}{simple:G.Simple}{a:Axis}{ε:ℝ}
variable (first:WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid:WilsonPositionProgramStageInvoice.Requested C.kit)(slow:WilsonWindowReportingPace.Slow C.kit)
    (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)(p:ℕ)(color:G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first paid slow in
theorem original {n:ℕ}(nonempty:0<n)(K:Set (Points n))(compact:IsCompact K):
    ∃ start:ℕ,∀ (m j i:X → ℕ)(w:X → ℕ → ℕ)
      (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach:∀x,WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀x,start ≤ m x)  →  ∀ (z:X → Fin n →  Cover)(c:X → Four ℝ),
      (∀x,c x∈(D.step (i x)).Box)  →  (∀x,(D.step (i x)).rel (z x) (c x)∈K)  → 
      let S:=WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∀F:Tent j,Notebook S Y G branch color (Rocket.native j) F p  → 
      ∀ (I:Type)[Fintype I][LinearOrder I](child:I → Fin n)(d:I → ℕ)(trees:∀x,(D.step (i x)).p.Tree)
        (q:ℕ),q ≤ p  →  ∀strength:ℕ,∃threshold:ℕ,∀x,threshold ≤ i x  → 
        1 ≤ C.family.path.levels.clock.hatBeta (m x)  → 
        RG16.Lambda C.family.path.levels (m x) ≤ (i x:ℝ)*Real.log D.ratio  → 
        ∀ δ:ℝ,0<δ  →  ∀ᶠ per in atTop,∀ (g:ℝ)(v:∀j,(C.family.labels.level (d j)).Coeff),
        ‖PowerSeries.coeff q (WilsonOriginalPublicTrialNormalization.series C d g v (z x ∘ child)
              (D.step (i x)).p (trees x))-
            ∑b,WilsonOriginalPublicTrialFigure.weight C d g v b*
              shifted C d q b (source C D m j w blocks branch F (fun x=>z x ∘ child) d x per)‖ₑ  ≤ 
          (ENNReal.ofReal ((D.step (i x)).spacing^strength)+ENNReal.ofReal δ)*
            ∑b,‖WilsonOriginalPublicTrialFigure.weight C d g v b‖ₑ:=by
  obtain ⟨H,_,start,ready⟩:=WilsonPositionProgramConsultedFaces.original (X:=X) C D first paid slow branch p color nonempty K compact
  refine ⟨start,?_⟩
  intro m j i w blocks reach old z c box room S F file I _ _ child d trees q hq strength
  let B:=∀k,(C.family.labels.level (d k)).Index
  let L:=WilsonPositionProgramInfraredMeter.wallet C D m j w i H
  let deg:=fun b:B=>Kick.depthF univ d b
  let tree:=fun (x:X)(b:B)=>WilsonPositionProgramCopyTop.normalized C (D.step (i x)).p d (z x ∘ child) b (trees x)
  let lo:=fun (x:X)(b:B)=>stopped C D m j w blocks branch F (fun x=>z x ∘ child) d x (q-deg b) b
  let gap:=fun (b:B)(x:X)=>‖PowerSeries.coeff ((q-deg b)+deg b) (tree x b)-lo x b‖ₑ
  have each(b:B):Carry L (Rocket.wage S Y branch F (final j) (1/2)) (gap b):=
    ready m j i w blocks reach old z c box room F file I child d b trees (q-deg b) ((Nat.sub_le ..).trans hq)
  obtain ⟨threshold,priced⟩:=WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach branch F H
    (Carry.sum univ gap (fun b _=>each b)) strength
  refine ⟨threshold,?_⟩
  intro x high mature age δ positive
  have near:=WilsonOriginalPublicFigurePeriod.purchased C D m j w blocks branch F (fun x=>z x ∘ child) d x q δ positive
  filter_upwards [near] with per paidPeriod
  intro g v
  rw [WilsonOriginalPublicTrialNormalization.filed,map_sum]
  simp only [PowerSeries.coeff_smul,smul_eq_mul]
  apply WilsonOriginalPublicFigurePeriod.tested C d _ _
    (fun b=>shifted C d q b (source C D m j w blocks branch F (fun x=>z x ∘ child) d x per)) _ _ _ paidPeriod
  intro b
  by_cases pos:deg b ≤ q
  · rw [WilsonOriginalPublicFigurePeriod.shifted,if_pos pos]
    have bit:gap b x ≤ ∑a:B,gap a x:=single_le_sum (f:=fun a=>gap a x) (fun _ _=>bot_le) (mem_univ b)
    have bank:=bit.trans (priced x high mature age)
    simpa only [gap,lo,Nat.sub_add_cancel pos] using bank
  · rw [WilsonOriginalPublicFigurePeriod.shifted,if_neg pos,WilsonPositionProgramInversionRank.original C _ d (z x ∘ child) b
      (trees x) q (Nat.lt_of_not_ge pos),sub_self,enorm_zero]
    exact bot_le

end YM.Integration.WilsonOriginalPublicFigureRate
end
