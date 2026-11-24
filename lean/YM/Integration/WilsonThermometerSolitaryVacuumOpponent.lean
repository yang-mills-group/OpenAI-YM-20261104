import YM.Integration.WilsonThermometerOccupiedGallery

/-! The appointed hard address book with exactly its quiet coefficients and a newly enrolled ordinary pupil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryVacuumOpponent
open Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Extra.Trajectories Next.Rank.Exponential
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
open MergeProof.Accent Hard WilsonThermometerOccupiedGallery
local notation "J₃" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{X A B:Type}{W:Rep G n}{o:Fin 3→Site n}
def offer (E:Lamps X B G W.p o (J₃))(P:Gallery X A o W (J₃)):Gallery X B o W (J₃):=
  gallery 0 ⟨E,P.K⟩

theorem original (E:Lamps X B G W.p o (J₃))(P:Gallery X A o W (J₃))
    (w:Fin 3→ℝ)(wp:∀v,0<w v){κ:ℝ}(old:P.K.Paid w W.p.B W.p.supportExponent κ):
    (offer E P).K.Paid w W.p.B W.p.supportExponent κ ∧
    ∀x U,(offer E P).density x U=(W.eval U:ℂ) • Poly.pass (E.log x U):=by
  have invested:=WilsonThermometerOccupiedHard.paid P.K (0:ℂ) (le_refl (1:ℝ)) (by norm_num) wp old
  have zero:(offer E P).K.Paid w W.p.B W.p.supportExponent κ:=by
    change (WilsonThermometerOccupiedHard.hard 0 P.K).Paid w W.p.B W.p.supportExponent κ
    simpa only [one_mul] using invested
  exact ⟨zero,fun x U=>origin ⟨E,P.K⟩ x U w wp zero⟩

end YM.Integration.WilsonThermometerSolitaryVacuumOpponent
