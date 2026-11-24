import YM.Integration.WilsonConditionalTaylorWheelVacuumHistory
import YM.Integration.WilsonConditionalTaylorWheelIssuedResponse
import YM.Integration.WilsonConditionalTaylorMarkedPrefix

/-! The funded old interacting action in the full signed marked
conditional can now be replaced by the independently prescribed finite
periodization, on every actual forest, period and nonzero background. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelFiledMark
open Function Filter Matrix Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonConditionalTaylorWheelKernel
open WilsonConditionalTaylorWick PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Matrix Topology
variable {G:Gauge}

theorem nonlinear {c f:Side} {S:StepData c f} (F:Forest S.ratio) (t:S.Choices) (O:ChartRatio G)
    {A B:Pap (wire G f)} {E:ℕ} (h:Through E A B):
    Through E (WilsonMovingFiniteConditional.interaction (Reef.flush F t O A))
      (WilsonMovingFiniteConditional.interaction (Reef.flush F t O B)):=by
  have before:Through E (Reef.vacuumU t A) (Reef.vacuumU t B):=by
    intro d hd
    simp only [Reef.vacuumU,map_sub,coeff_map,h d hd]
  have stage:=Through.change_congr (insertAt ℝ (motor (Reef.graft F (G:=G)))) before
  have now:Through E (Reef.flush F t O A) (Reef.flush F t O B):=by
    intro d hd
    simp only [Reef.flush,map_add,Wick.roam,stage d hd]
  have scalar:PowerSeries.C (coeff 0 (Reef.flush F t O A))=PowerSeries.C (coeff 0 (Reef.flush F t O B)):=by
    rw [now 0 (Nat.zero_le E)]
  unfold WilsonMovingFiniteConditional.interaction
  rw [scalar]
  exact now.sub (Through.exact_eq _ _)

variable (D:Stage G)
local notation "V" => D.R.family.path.levels
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
local notation "form" => freeForms V D.N (D.j+1)
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA V D.N D.j)
local notation "old" => Winding.emera (actionW V D.R.metals.O D.N (D.j+1)) fine
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (D.R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(D.R.family.path.levels.blocks k 0).branches)

theorem normalized (simple:G.Simple) (u:G.ColorIndex) (E:ℕ)
    (history:WilsonConditionalTaylorWheelVacuumHistory.Identified D.R u D.N (D.j+1) E)
    (q:ℕ) (w:PChart G fine) (shape:shellK q w) (pure:∀e,Pure (w e)) (y:wire G coarse→ℝ):
    let W:=Dove.model V wood b D.R.metals.O u D.N (D.j+1)
    Through E (glimpse y (Blue.flash (reed op D.forest form mean D.R.metals.O old q w)))
      (quotient (WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest)
        (WilsonConditionalTaylorWheelResponse.center (G:=G) op D.forest mean y) (saddle D).q
        (WilsonMovingFiniteConditional.interaction (Reef.flush D.forest D.tag D.R.metals.O (Mesa.stone W fine)))
        (Reef.seat D.forest (Blue.flash w))):=by
  intro W
  have prior:Through E (-Blue.flash old) (Mesa.stone W fine):=
    WilsonConditionalTaylorWheelInputTruncation.retained D.R simple D.N (D.j+1) (Nat.succ_le_iff.mpr D.live) W E
      (fun e he r hr=>history e he r (by omega)) fine
  rw [WilsonConditionalTaylorWheelIssuedResponse.original D simple q w shape pure y]
  exact WilsonConditionalTaylorMarkedPrefix.quotientPaid _ _ _
    (((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).positive D.forest D.tag)
    (WilsonMovingFiniteConditional.origin _) (WilsonMovingFiniteConditional.origin _) (nonlinear _ _ _ prior)
    (Through.exact_eq _ _)

end YM.Integration.WilsonConditionalTaylorWheelFiledMark
end
