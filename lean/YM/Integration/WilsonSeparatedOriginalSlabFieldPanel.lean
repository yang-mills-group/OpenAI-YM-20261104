import YM.Integration.WilsonSeparatedOriginalSlabFolioCensus
import YM.Integration.WilsonSeparatedOriginalSlabRootedCredit

/-! Finite signed profile on the original joint regulator, with rooted certificates for each one of its eight masked words. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFieldPanel
open Function Finset Lattice Wilson Labels RG Source RG05Readout.Address RG05Readout.Flatten PhysicalNext.Repeat.Legato
open RG16.Literal RG05Readout RG05Readout.Many RG05Readout.Pulse RG05Readout.Records Native RG.History
open WilsonSeparatedOriginalSlabBladeModule WilsonReportHarvestSlabLabels WilsonSeparatedOriginalSlabFolioAddress
open WilsonSeparatedOriginalSlabPhysicalBlade WilsonSeparatedOriginalSlabFolioCensus
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n N per:ℕ}(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))
set_option quotPrecheck false
local notation "C"=>R.family
local notation "Y"=>(C).path.rep N per

def word (o:Fin 3→Site ((C).side n per))(f:Fin 3→Body)(a:(Stock.census (Fin 3)).Mode)
    (U:Config G ((C).side N per)):ℂ:=∏i∈a.val,clinic C per N (s i) (v i) n (o i) (1,false) (f i) U

theorem continuous_word (o:Fin 3→Site ((C).side n per))(f:Fin 3→Body)(a:(Stock.census (Fin 3)).Mode):
    Continuous (word R (N:=N) s v o f a):=continuous_finsetProd _ fun i _=>clinic_cut (v i) (1,false) (o i) (f i)

def Returned (top:n≤N)(fee:ℝ)(o:Fin 3→Site ((C).side n per))(f:Fin 3→Body):Prop:=
  ∀ a,Filed (Y n) 0 (credit C N per 0 (word R s v o f a) n top) fee

def mass (J:ℕ)(Ψfee cap:ℝ)(r:ℝ)(m:ℕ):ℝ:=
  ‖premiums C s m n r‖*cap*((Lattice.box J).card:ℝ)^3*Ψfee

structure Panel (top:n≤N)(fee:ℝ)(Y₀:Config G ((C).side N per)→ℂ)(cap:ℝ) where
  I:Type
  finite:Fintype I
  site:I→Fin 3→Site ((C).side n per)
  test:I→Fin 3→Body
  weights:I→ℂ
  filed:∀i,Returned R s v top fee (site i) (test i)
  bound:letI:=finite; ∑i,‖weights i‖≤cap
  exact:letI:=finite; Y₀=∑i,weights i • word R s v (site i) (test i) WilsonReportHarvestSlabLabels.entire

end YM.Integration.WilsonSeparatedOriginalSlabFieldPanel
