import YM.Integration.WilsonIndependentMatchedOwnHomeMeasuredRoster
import YM.Integration.WilsonIndependentSpoutMasterReport

/-! Smooth site integration on the actual pinned full input. Every thermal
coefficient of the old output has its own honest continuous representative. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeCellRows
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol MeasureTheory
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonPositionProgramPinnedHearthHistory (pin)
open WilsonSeparatedPrefixMovingPinHearing (hear shiftHom)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{E W V:Credit}

def collect (Φ:Rarity d)(ε y:ℝ)(o:CellR):(Cover→Lounge)→ₗ[ℝ]ℝ where
  toFun f:=∑s∈canvasM Φ ε y, ε^4*∫z:CellR,Φ.ψ.val (Mer.address ε y o s z.val)*(f s z) ∂dayMeasure
  map_add' f g:=by
    have paid (f:Cover→Lounge)(s:Cover):Integrable (fun z:CellR=>Φ.ψ.val (Mer.address ε y o s z.val)*f s z) dayMeasure:=by
      have pos:Continuous (fun z:CellR=>Mer.address ε y o s z.val):=
        (Mer.address_cont ε y s).comp (continuous_const.prodMk continuous_id)
      exact (((scribble Φ.ψ le_rfl).continuous.comp pos).mul (f s).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [Pi.add_apply,ContinuousMap.add_apply,mul_add]
    simp_rw [integral_add (paid f _) (paid g _),mul_add,Finset.sum_add_distrib]
  map_smul' c f:=by
    change (∑s∈canvasM Φ ε y,ε^4*∫z:CellR,Φ.ψ.val (Mer.address ε y o s z.val)*(c*(f s z)) ∂dayMeasure)=
      c*∑s∈canvasM Φ ε y,ε^4*∫z:CellR,Φ.ψ.val (Mer.address ε y o s z.val)*(f s z) ∂dayMeasure
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro s _
    simp_rw [mul_left_comm (Φ.ψ.val _) c,integral_const_mul]
    ring

variable (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
local notation "A₀" => R.draws
local notation "O₀" => R.paid

def row (m c older K N:ℕ)(y:ℝ)(j:ℕ)(s:Cover):Lounge:=
  (cruises A₀ O₀ N (capP Q) K older (shifted
    (HearthC Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y) (pin R.draws.S c K s))).2 j 0 Fin.elim0

theorem placed (fund:HorizonP H R W V Q)(m c older K N:ℕ)(live:R.anchor ≤ K)(old:older ≤ K)(top:K ≤ N)
    (y:ℝ)(j:ℕ)(s:Cover)(z:CellR)(w:Fin 0→YForest G):
    row R Q φ b m c older K N y j s z=
      (hear R (capP Q) N c older s K (Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y z)).2 j 0 w:=by
  let raw:=HearthC Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y
  have auth:Auth (capP Q) raw:=Hearth_enter fund φ _ live top
  have source:locale z (cruises A₀ O₀ N (capP Q) K older (shifted raw (pin R.draws.S c K s)))=
    hear R (capP Q) N c older s K (Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y z):=by
    unfold hear locale
    rw [cruiseT (century z) R.draws old R.hG R.green top (auth.shifted _),ash_spans]
    rfl
  rw [Subsingleton.elim w Fin.elim0]
  exact congrArg (fun B:Era G ℝ=>B.2 j 0 Fin.elim0) source

def recorded (Φ:Rarity d)(yOut:ℝ)(o:CellR)(t m c older K N:ℕ):Cost:=
  PowerSeries.mk fun l=>collect Φ (paceT R.draws.S t c) yOut o
    (row R Q φ b m c older K N (paceT R.draws.S m c) l)

theorem coefficient (Q:Fin ((n+1)+1)→SealR G)(φ:Wilt Q)(b:Herit Q)(fund:HorizonP H R W V Q)
    (Φ:Rarity d)(yOut:ℝ)(o:CellR)(t m c older K N j:ℕ)(live:R.anchor ≤ K)(old:older ≤ K)(top:K ≤ N)(w:Fin 0→YForest G):
    PowerSeries.coeff j (recorded R Q φ b Φ yOut o t m c older K N)=
      WilsonIndependentMatchedOwnHomeMeasuredRoster.total R Q φ b Φ yOut o t m c older K N j 0 w:=by
  unfold recorded WilsonIndependentMatchedOwnHomeMeasuredRoster.total
  rw [coeff_mk]
  change (∑s∈_,_*∫z:CellR,_*row R Q φ b _ _ _ _ _ _ _ s z ∂dayMeasure)=_
  simp_rw [placed R Q φ b fund m c older K N live old top _ j _ _ w]

end YM.Integration.WilsonIndependentMatchedOwnHomeCellRows
end
