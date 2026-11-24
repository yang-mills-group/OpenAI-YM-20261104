import YM.Integration.WilsonIndependentFittedNumericalProduct
import YM.Integration.WilsonOriginalPublicPlantedTaylorPortfolio

/-! The two numerical orders on one filed sample use exactly the same fitted vectors. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedDirectoryNode
open Filter Set Finset Function Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open PowerSeries FVA2 FVA2.Register MS MS.Land MS.Menus MS.Theater Local.Physical
open MS.WilsonBridge.Coupling MS.Book MS.Book.Program
open WilsonOriginalPublicPlantedPivotFields (plant)
open WilsonPositionProgramPublicDirectoryCoin (drawValue)
open WilsonPositionProgramPublicDirectoryTensor (filed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedNumericalProduct
open scoped Topology BigOperators Classical

variable {G:Gauge}(Z:WilsonPrescription G)(β:Deck G){n d:ℕ}
local notation "Γ" => Glyph β d

def arm (j:ℕ)(s:Sample n)(i:Fin n)(a:Γ):Bare.Series (Z.scheme.tree s.F.p) G:=
  plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s i (Theater.Daylight β d a)

theorem point {j B:ℕ}(P:Handoff.Directory Z j B)(q:ℕ)
    (cap:Handoff.Directory.budget G n d+q≤B)(s:Sample n)(board:s.F=Z.run.step j)
    (a:Fin n→Γ)(u:ℝ):
    cash q u (pivot Z.scheme s (arm Z β j s) a)=
      drawValue Z (fun i=>Theater.Daylight β d (a i)) q P u s.layout:=by
  rw [WilsonOriginalPublicPlantedPivotFields.drawn β Z P s _ board q cap]
  unfold cash pivot arm
  exact sum_congr rfl (fun _ _=>mul_comm ..)

theorem purchased {j B:ℕ}(P:Handoff.Directory Z j B)(J Q:ℕ)
    (cap:Handoff.Directory.budget G n d+J≤B)(s:Sample n)(board:s.F=Z.run.step j)
    (D:Fin n→Γ→PowerSeries ℂ)(u:ℝ):
    numerical Z.scheme s (arm Z β j s) D Q J u=
      drawValue Z (filed d β (fun i a=>cash Q u (D i a))) J P u s.layout:=by
  rw [WilsonPositionProgramPublicDirectoryTensor.original P d s.layout β]
  unfold numerical
  apply sum_congr (by ext; simp)
  intro a _
  rw [point Z β P J cap s board a u]

variable {sg:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z sg M T dial)
    {K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n)
    (l:Filter ℝ){t:ℝ→ℝ}(pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))

include H compact apart pos small in
theorem original (J Q:ℕ)(order:J≤Q)(k:ℕ)(C:ℝ){δ:ℝ}(toll:0<δ):
    ∃i₀:ℕ,∀ᶠ r in l,∀j≥i₀,(j:ℝ)≤C*(-Real.log (t r))^k →
      ∃P:Handoff.Directory Z j (Handoff.Directory.budget G n d+Q),
      ∀s:Sample n,s.F=Z.run.step j → welcome s → familiar s∈K →
      ∀u:ℝ,|u|≤8*t r → ∀D:Fin n→Γ→PowerSeries ℂ,
        ‖cash Q u (fitted Z.scheme s (arm Z β j s) D)-
          drawValue Z (filed d β (fun i a=>cash Q u (D i a))) J P u s.layout‖≤
          ((n:ℝ)+1)*|u|^(Q+1)*gross Z.scheme s (arm Z β j s) D Q+
          wage D Q u*(δ*(t r)^J):=by
  choose first payable using (fun a:Fin n→Γ=>WilsonOriginalPublicPlantedTaylorTail.directory
    Z H (fun i=>Theater.Daylight β d (a i)) compact apart l pos small J Q order k C toll)
  refine ⟨univ.sup first,?_⟩
  filter_upwards [Filter.eventually_all.mpr payable,small.eventually
    (gt_mem_nhds (show (0:ℝ)<1/8 by norm_num))] with r rates cold
  intro j late clock
  obtain ⟨P⟩:=H.packets j (Handoff.Directory.budget G n d+Q)
  refine ⟨P,?_⟩
  intro s board welcome paid u size D
  have low:Handoff.Directory.budget G n d+J≤Handoff.Directory.budget G n d+Q:=by omega
  rw [←purchased Z β P J Q low s board D u]
  have tail(a:Fin n→Γ):
      ‖cash Q u (pivot Z.scheme s (arm Z β j s) a)-
        cash J u (pivot Z.scheme s (arm Z β j s) a)‖≤δ*(t r)^J:=by
    rw [point Z β P Q le_rfl s board a u,point Z β P J low s board a u]
    exact rates a j ((le_sup (f:=first) (mem_univ a)).trans late) clock P le_rfl s board
      welcome paid u size
  simpa only [Fintype.card_fin] using retained Z.scheme s (arm Z β j s) D Q J
    (show |u|≤1 by linarith) tail

end YM.Integration.WilsonIndependentFittedDirectoryNode
