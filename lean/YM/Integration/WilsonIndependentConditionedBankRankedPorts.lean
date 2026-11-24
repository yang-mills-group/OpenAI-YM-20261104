import YM.Integration.WilsonIndependentConditionedBankPhysicalPorts
import YM.Integration.WilsonIndependentNotebookRawSeat

/-! An original fitted receipt pays either its report print or its ordinary angular-rank group word. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRankedPorts
open Function Filter Finset Lattice RG Wilson Source Labels XSpace XSpace.Rose XSpace.Cirrus
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain PowerSeries
open WilsonIndependentConditionedBankSeats (Resident raw restored submitted)
open WilsonIndependentNotebookConstantSeat (issue)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentNotebookRawSeat (component)
open WilsonOriginalPhysicalFruitVerse (written)
open scoped BigOperators Classical
variable {G:Gauge}{R:Run G}{d f K N per target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}

def offered (F:Labels.Frame G d)(plain im:Bool)(z:F.Coeff):Verse F:=
  if plain then written F z (component im) else issue F im z

def incoming (r:Resident R d f K N per target up live η)(plain im:Bool):Verse (R.family.labels.level d):=
  offered (R.family.labels.level d) plain im (((R.family.S.a K/R.family.S.a f)^d) • raw r)

theorem budget (r:Resident R d f K N per target up live η)(plain im:Bool)(e:ℕ)
    (A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0 ≤ A i):
    charge e (incoming r plain im) A ≤ charge e (submitted r im) A:=by
  cases plain
  · exact le_rfl
  · exact WilsonIndependentNotebookRawSeat.charged _ im e A non

theorem original (r:Resident R d f K N per target up live η)(I₀:Initialize G)(survey plain im:Bool)
    {D e:ℕ}(fit:d<D)(A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0 ≤ A i):
    let F:=R.family.labels.level d;let δ:=R.family.S.a K/R.family.S.a f
    let filed:=plate (sectionAt R I₀ survey d) fit
    let old:=offered F plain im (raw r)
    Shrine filed (incoming r plain im)=δ^d • Shrine filed old ∧
      charge e (incoming r plain im) A=δ^d*charge e old A ∧
      charge e (incoming r plain im) A ≤ restored (e:=e) A r*δ^(-η):=by
  intro F δ filed old
  have mass:=(WilsonIndependentConditionedBankSeats.paid (e:=e) r I₀ survey fit A non im).2.2
  have bought:=(budget r plain im e A non).trans mass
  refine ⟨?_,?_,bought⟩
  · cases plain
    · exact (WilsonIndependentConditionedBankSeats.paid (e:=e) r I₀ survey fit A non im).1
    · exact (WilsonIndependentNotebookRawSeat.original R I₀ survey fit e A non r.before up live r.axis r.source
        r.paid r.arm r.same r.phase im).1
  · cases plain
    · exact (WilsonIndependentConditionedBankSeats.paid (e:=e) r I₀ survey fit A non im).2.1
    · exact (WilsonIndependentNotebookRawSeat.original R I₀ survey fit e A non r.before up live r.axis r.source
        r.paid r.arm r.same r.phase im).2.1

end YM.Integration.WilsonIndependentConditionedBankRankedPorts
