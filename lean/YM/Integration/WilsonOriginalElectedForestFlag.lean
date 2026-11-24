import YM.Integration.WilsonOriginalArbitraryForestColumn
import YM.Integration.WilsonOriginalFoldedFiledForest

/-! The actual independently identified quiet and complete marked step on any original forest and tag. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalElectedForestFlag
open Function Finset Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical
variable {G:Gauge}
open WilsonNeutralNormalizedForestStep (chamber)
open WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Soil

private theorem relocated {n f:Side}(S:StepData n f)(P:Patch)(K:KernelChoices)
    (hp:S.patch=P)(hk:S.kernel=K)(F:Forest (S).ratio):
    ∃F':Forest (Flat.primary P K n).ratio, HEq F F' ∧ ∀(u:PoleRows S.patch)(v:PoleRows P),HEq u v →
      ∀(Y:FreeResolvent.FaceRow)(O:ChartRatio G)(U T:Crude G)(q:ℕ),
      reed S F Y (installed S.ratio u) O (U f) q (T f)=
        reed (Flat.primary P K n) F' Y (installed (Flat.primary P K n).ratio v) O (U (n*P.L)) q (T (n*P.L)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p
  subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  refine ⟨F,HEq.rfl,?_⟩
  intro u v row Y O U T q
  cases eq_of_heq row
  rfl

variable (R:Run G)(N i per:ℕ)
local notation "V" => R.family.path.levels
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
local notation "br" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "n₀" => coarse R i per
local notation "f₀" => fine R i per
local notation "P₀" => destination V N i

theorem original (u:G.ColorIndex)
    (tags:∀j n,(primary ((V).clock.op j 0).patch (V).clock.kernel n).Choices)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:i<N)(F:Forest (S).ratio):
    ∃F':Forest (Flat.primary (P₀).patch (V).clock.kernel n₀).ratio, HEq F F' ∧
      ∀(t:(Flat.primary (P₀).patch (V).clock.kernel n₀).Choices)(q:ℕ)(T:Crude G),
      shellK q (T (n₀*(P₀).L)) → (∀d,Pure (T (n₀*(P₀).L) d)) →
      let U:=Mesa.stone (Dove.model V wood br R.metals.O u N (i+1)) (n₀*(P₀).L)
      Blue.flash (WilsonOriginalFoldedMarkedRightColumn.filed R N i per F q (T f₀))=
        Orb.flag (chamber P₀ (br i) n₀ F' t) (Reef.flush F' t R.metals.O U)
          (Reef.seat F' (Blue.flash (T (n₀*(P₀).L)))):=by
  obtain ⟨F',hF,transfer⟩:=relocated S (P₀).patch (V).clock.kernel rfl rfl F
  refine ⟨F',hF,?_⟩
  intro t q T bound pure U
  let W:=Dove.model V wood br R.metals.O u N (i+1)
  let f:=n₀*(P₀).L
  let X:=emera (actionW V R.metals.O N (i+1)) f
  let Y:=freeForms V N (i+1)
  have prior:=(WilsonVacuumPreResetIndependentHistory.original R u simple v funded tags N (i+1) live).1
  have fold:-Blue.flash X=Mesa.stone W f:=Through.top fun e=>
    WilsonVacuumPreResetCanonicalPrefix.retained R simple N (i+1) live W e (fun a _ r _=>prior a r) f
  have dossier:=(Dove.genu V wood br R.metals.O u R.alloy.B.ratio simple (i:=i+1) (N:=N) live).toStory
  have head:coeff 0 (-Blue.flash X)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (P₀).wing f):=by
    rw [fold]
    obtain ⟨s,C,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos (P₀).legal
    exact Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  have old:=emera_far V simple R.alloy.B.ratio (N:=i+1) (m:=N) live f
  have raw:=WilsonOriginalArbitraryForestColumn.normalized P₀ (br i) n₀ F' t R.metals.O R.alloy.B.ratio
    ((V).clock.adm i) Y rfl X old.1 head (age_sym V ..) old.2 q (T f) bound pure
  have lift:=transfer (predictionA V N i) (predictionA V N i) HEq.rfl Y R.metals.O
     (emera (actionW V R.metals.O N (i+1))) T q
  exact (congrArg Blue.flash lift).trans (raw.trans (congrArg (fun Z=>Orb.flag (chamber P₀ (br i) n₀ F' t)
    (Reef.flush F' t R.metals.O Z) (Reef.seat F' (Blue.flash (T f)))) fold))

end YM.Integration.WilsonOriginalElectedForestFlag
