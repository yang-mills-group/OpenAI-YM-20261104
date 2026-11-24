import YM.Integration.WilsonOriginalPublicTrialPhaseBirth
import YM.Integration.WilsonCloseCaptureAddress
import YM.RG05Readout.Address.Lit

/-! The original issued one-step address applies to the coefficient that
carries the uncut fitted K word and its actual old hard profile. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFirstRide
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets
open Extra.Multi MergeProof.Ribbons
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
variable {m N per:ℕ}{T:Campaign R}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "S" => (C).path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per

theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)(book:Campaign.Pillars R T)
    (live:m<N)(d:ℕ)(grade:d+3≤(A).clock.J m)(o:Site ((C).side (m+1) per))
    (home:(O).ratio.parent o=0)(v:(C).label d)
    (hit:Push.Local.hitWidth (Q).p*Push.Local.kappa (S) m≤1)(fine:Push.Local.kappa (S) (m+1)≤1)
    (small:((((C).localSection d).footprint o).card:ℝ)*(S).levels.clock.forcedAllowance (m+1)≤1):
    let F:=(C).labels.level d
    let loc:=(C).localSection d
    let D:=loc.footprint o
    let r:=(P).p.mass D 0 + 2*(D.card:ℝ)*Push.Local.kappa (S) (m+1)*
      (P).p.mass D (BasisCost.price loc*F.coeffSize (names R d N per (m+1) v))
    let L:=(C).S.block m
    let c:=R.y ((A).clock.J (m+1))
    let α:=Doors.rate ((A).S.block m)
    let β:=2*(Real.exp ((A).params (m+1)).supportExponent*PhysicalNext.Repeat.Cub.title G ((A).params (m+1)))
    let w:=F.coeffSize v
    let ℓ:=((L.val:ℝ)^d)*c
    ∃ q:Coefficient F ((C).side (m+1) per),q.x=v ∧ q.Format o (C).params (P) ∧
      (∀U,q.density o loc (P) U=((P).eval U:ℂ)*uncut R d N per (m+1) o v U) ∧
      q.remBound o (P) (Push.Local.kappa (S) (m+1)) r ∧
      (∃ ψ,Attainment (P).p o ψ (reservedMass (P).p D (BasisCost.price loc*F.coeffSize (names R d N per (m+1) v))) ∧
        profile (P).activities q.forced=hook (P).activities (P).p.threshold ψ) ∧
      ∃ k:Coefficient F ((C).side m per),k.Format 0 (C).params (Q) ∧
        k.remBound 0 (Q) (Push.Local.kappa (S) m) (ℓ*w+α*r) ∧ F.coeffSize k.x≤ℓ*w+α*r ∧
        ∃ price:ℝ, price=(1+ℓ+β)*w+(2+α)*r ∧
          Ride (O) o 0 (R.doors N per m live) ((L.val:ℂ)^d) (invoice q o loc (P)) (invoice k 0 loc (Q)) price:=by
  intro F loc D r L c α β w ℓ
  obtain ⟨q,eq,fmt,writes,rem,hook⟩:=WilsonOriginalPublicTrialPhaseBirth.original R book live d o v small
  obtain ⟨_,sale⟩:=WilsonCloseCaptureAddress.issued R hG purchase d m N per live grade hit fine
  obtain ⟨heading,a,ticket,_⟩:=WilsonCloseCapturePositions.positions R hG purchase d N m per live grade
  have wage:(P).p.supportExponent=((A).params (m+1)).supportExponent:=
    congrArg BudgetPoint.supportExponent (R.makes.wilson.represents N per (m+1) live).vac
  rw [wage] at ticket
  obtain ⟨k,format,tariff,step,size⟩:=RG05Readout.Address.rough (C) N m per d o (R.doors N per m live)
    R.makes live home ticket sale.a_pos q sale.posp sale.b_pos fine fmt rem
  exact ⟨q,eq,fmt,writes,rem,hook,k,format,by simpa only [eq] using tariff,by simpa only [eq] using size,
    _,by rw [eq],step⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseFirstRide
end
