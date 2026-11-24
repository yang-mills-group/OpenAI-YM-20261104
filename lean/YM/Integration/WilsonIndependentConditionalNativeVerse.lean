import YM.Integration.WilsonIndependentConditionalNativeArm
import YM.Integration.WilsonIndependentConditionalThermalCap

/-! The real enrolled circuit and Mer reporter have a common finite-degree
marked transfer when the positive vacuum rows are filed in the same chart. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalNativeVerse
open Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open RegulatorIR.Oracle RegulatorIR.Quadratic RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Ledger
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonIndependentConditionalUnshiftedExit WilsonIndependentConditionalCoordinateHeat
open WilsonIndependentConditionalNativeLinks
open scoped BigOperators Matrix Classical
variable {G:Gauge}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}
variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
variable (R:WilsonIndependentPublicFreeTrain.Matches A C K s w)
variable (Y:Program K)(Z:∀P:Patch,P.Branches K G)(t:Page M→RegulatorIR.Binding.Scale)
variable (f:Flap M)(hw:f.volW=w)
local notation "N₀" => s+M w
local notation "m₀" => s+(M w-(f.offset+1))
local notation "P₀" => loose A m₀
local notation "D₀" => C.devices Y G Z t f
include R hw

theorem submitted {d:ℕ}(T U:Orders (Foot G))(W:Orders (Cloth (Hinge G (P₀).L)))(H:Pal ℝ (YForest G))
    (prior:∀e≤d,∀ r,0<r→(D₀).jVac T e r=row (joint G P₀) (W e r))
    (mark:∀e≤d,U e=ranks (coarse G) (H e))(k:ℕ){e:ℕ}(he:e≤d)(r:ℕ):
    let Γ:=WilsonIndependentConditionalUnshiftedQuiet.kernel P₀ (shuttleM (conditional A N₀ m₀))
    let pred:=post P₀ (shuttleM (feedA A N₀ m₀))
    (D₀).each k T U e r=row (coarse G) (scoop (Packet.draft pred.transpose
      (endHeat k Γ (logHeat Γ W false) (slidesJ P₀ 0 H) e r))):=by
  intro Γ pred
  let q:=joint G P₀
  let Φ:Orders (KFoot G):=fun i j=>offer (Function.Embedding.inl:Foot G↪KFoot G) (U i j)
  have ink (i)(hi:i≤d):Φ i=orders q (slidesJ P₀ 0 H) i:=by
    funext j
    change offer _ (U i j)=_
    rw [mark i hi]
    exact (WilsonIndependentConditionalNativeArm.original P₀ H i j).symm
  have inc:=WilsonIndependentConditionalThermalCap.original (D₀).line prior ink k he
  change (D₀).pullI (endHeat k (D₀).line (logHeat (D₀).line ((D₀).jVac T) false) Φ e r)=_
  rw [congrFun inc r,WilsonIndependentConditionalNativeLinks.covariance R Y Z t f hw]
  change (D₀).pullI (endHeat k (line q Γ) (logHeat (line q Γ) (orders q W) false) (orders q (slidesJ P₀ 0 H)) e r)=_
  rw [WilsonIndependentConditionalCoordinateVerse.marked]
  exact WilsonIndependentConditionalNativeLinks.pull R Y Z t f hw _

theorem original {d k:ℕ}{Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (source:Era G ℝ)(valid:Auth k source)(T U:Orders (Foot G))
    (prior:∀e≤d,∀r,0<r→(D₀).jVac T e r=
      row (joint G P₀) (stellar P₀ K Ñ 0 (actionW A Ñ N₀ (m₀+1)) e r))
    (mark:∀e≤d,U e=ranks (coarse G) (source.2 e)){e:ℕ}(he:e≤d)(r:ℕ):
    row (coarse G) ((verseI A Ñ m₀ N₀ k source).2 e r)=
      Blue.mix (ratioHigh A Ñ N₀ m₀) ((D₀).each k T U) e r:=by
  have small:f.offset<M w:=hw ▸ f.ok
  have live:m₀<N₀:=by omega
  rw [WilsonIndependentConditionalMerReceiver.original A simple ratio live source valid]
  funext z
  simp only [Blue.mix,row,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have ih:i≤d:=by have:=Finset.mem_range.mp hi;omega
  apply congrArg (fun y:ℝ=>_ • y)
  let V:=stellar P₀ A.clock.kernel Ñ 0 (actionW A Ñ N₀ (m₀+1))
  have entry (j)(hj:j≤d)(l)(hl:0<l):(D₀).jVac T j l=row (joint G P₀) (V j l):=by
    unfold V;rw [R.kinetic];exact prior j hj l hl
  have eq:=submitted R Y Z t f hw T U V source.2 entry mark k ih r
  exact (congrFun eq z).symm

end YM.Integration.WilsonIndependentConditionalNativeVerse
