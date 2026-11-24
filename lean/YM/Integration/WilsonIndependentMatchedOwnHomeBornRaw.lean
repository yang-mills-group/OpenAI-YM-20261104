import YM.Integration.WilsonIndependentMatchedOwnHomePanel
import YM.Integration.WilsonIndependentMatchedOwnHomeReportedShell
import YM.Integration.WilsonSeparatedPrefixMovingPinnedRaw

/-! Stop the actually submitted whole two-home product in the original
kinetic chart. On its own birth date this is the paid joint raw Gram row. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeBornRaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedOwnHomePanel (born)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonIndependentMatchedOwnHomeReportedShell (reading)
open scoped BigOperators Topology Classical
open MeasureTheory
variable {G:Gauge}{H:Hol G}{n D e:ℕ}{E W V:Credit}
variable (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(α:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(Φ:Rarity D)(y:ℝ)(o:CellR)

theorem self (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(t m b older N j r:ℕ)(w:Fin r→YForest G)
    (enrolled:R.anchor ≤ N)(past:older ≤ N):
    born R Q F α ψ X Y Φ y o t m b older N N j r w=raw R Q F α ψ X Y Φ y o t m b older N j r w:=by
  unfold born WilsonSeparatedPrefixMovingPinCanvas.total WilsonSeparatedPrefixMovingPinnedRaw.raw
  apply Finset.sum_congr rfl;intro s _
  congr 1;apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
  apply congrArg (fun c:ℝ=>Φ.ψ.val (Mer.address (paceT R.draws.S t b) y o s z.val)*c)
  exact congrArg (fun U:Era G ℝ=>U.2 j r w)
    (WilsonIndependentMatchedOwnHomePanel.placed R Q F α ψ X Y roster far t m b older N N (paceT R.draws.S m b) s z enrolled past le_rfl)

def measured (t m b older K N j:ℕ)(g ρ:ℝ)(w:Fin 0→YForest G):ℂ:=
    reading R.draws R.paid N m older j g fun l=>(paceT R.draws.S m t^F.h)⁻¹*
      (ρ^4*born R Q F α ψ X Y Φ y o t m b older K N l 0 w)

theorem paid (H:Hol G)(F:SealR G)(e:ℕ)(E W V:Credit):
    ∃clock:Credit,∀(R:Realm G (e+1) E)(_fund:PassportC H R F W V)
    (Q:Fin (n+1)→SealR G)(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(Φ:Rarity D)(y:ℝ)(o:CellR)
    (t m b older K N:ℕ),R.anchor ≤ older → older ≤ m → m ≤ K → K ≤ N →
    ∀(J:ℕ)(g ρ upper completed retained:ℝ)(w:Fin 0→YForest G),J ≤ e → |g| ≤ 1 →
    let T:=paceT R.draws.S m t
    (∀l ≤ e,‖ρ^4*raw R Q F α ψ X Y Φ y o t m b older N l 0 w‖ ≤ upper) →
    (∀l ≤ e,‖raw R Q F α ψ X Y Φ y o t m b older N l 0 w-
      panel R Q F α ψ X Y Φ y o t m b older N K l 0 w‖ ≤ completed) →
    (∀l ≤ e,‖(T^F.h)⁻¹*(panel R Q F α ψ X Y Φ y o t m b older N K l 0 w-
      born R Q F α ψ X Y Φ y o t m b older K N l 0 w)‖ ≤ retained) →
    ‖measured R Q F α ψ X Y Φ y o t m b older K N e g ρ w-
      measured R Q F α ψ X Y Φ y o t m b older K N J g ρ w‖ ≤ 
      (Finset.Ico (J+1) (e+1)).card*|g|^(J+1)*((e+1)*clock.buy (Compar R.draws.S R.y older m)*
        ((T^F.h)⁻¹*upper+|ρ^4| *((T^F.h)⁻¹*completed+retained))):=by
  obtain ⟨C,price⟩:=WilsonIndependentMatchedOwnHomeReportedShell.original H F e E W V
  refine ⟨C,?_⟩
  intro R fund Q α ψ X Y Φ y o t m b older K N old past opened top J g ρ upper completed retained w order small T fine crossing joins
  apply price R fund N m older old past (opened.trans top) _ _ _ J g order small
  intro l hl
  let z:=born R Q F α ψ X Y Φ y o t m b older K N l 0 w
  let x:=raw R Q F α ψ X Y Φ y o t m b older N l 0 w
  let f:=panel R Q F α ψ X Y Φ y o t m b older N K l 0 w
  let a:=(T^F.h)⁻¹
  have pos:0 ≤ a:=inv_nonneg.mpr (pow_nonneg (pace_pos ..).le _)
  change ‖a*(ρ^4*z)‖ ≤ _
  have signed:a*(ρ^4*z)=a*(ρ^4*x)-ρ^4*(a*(x-f))-ρ^4*(a*(f-z)):=by ring
  rw [signed]
  apply ((norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)).trans
  rw [norm_mul,Real.norm_of_nonneg pos,norm_mul (ρ^4) (a*(x-f)),norm_mul (ρ^4) (a*(f-z)),
    norm_mul a (x-f),Real.norm_of_nonneg pos,Real.norm_eq_abs]
  calc
    _ ≤ a*upper+|ρ^4| *(a*completed)+|ρ^4| *retained:=by
      apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left (fine l hl) pos)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (crossing l hl) pos) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left (joins l hl) (abs_nonneg _))
    _=_:=by ring
end YM.Integration.WilsonIndependentMatchedOwnHomeBornRaw
end
