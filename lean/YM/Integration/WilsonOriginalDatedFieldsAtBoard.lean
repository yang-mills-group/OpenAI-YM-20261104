import YM.Integration.WilsonOriginalOpticalCouplingFares
import YM.Integration.WilsonOriginalPhysicalFieldsAtBoard

/-! The literal microscopic Wilson fields and the independently filed compact trial on the same decoder. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalDatedFieldsAtBoard
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open Source Labels
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators

open WilsonRootedKioskOccupiedSlip
variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {V:Type}[DecidableEq V][Fintype V](marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j

open WilsonOriginalPhysicalFieldsAtBoard
structure Degree where
  clock : ℕ
  inverse : ℕ

def Degree.pole (d:Degree):ℕ:=2*d.clock+d.inverse+1

def pound (d:Degree)(C:ℝ)(N per upper lower:ℕ):ℝ:=
  C*(H upper)^d.clock*((regulatorRun R.family N per lower)⁻¹)^d.inverse

include simple in
theorem restored (d:Degree)(C:ℝ)(cp:0 ≤ C)(t:ℕ):∀ᶠ b:ℕ in atTop,∀{N per K i j:ℕ},
    b ≤ i → i ≤ K → b ≤ j → j ≤ K → K ≤ N → R.family.S.a b/R.family.S.a K ≤ (H b)^t →
    pound R d C N per i j ≤ ((regulatorRun R.family N per b)^d.pole)⁻¹:=by
  simpa only [pound,Degree.pole,inv_pow] using WilsonOriginalOpticalCouplingFares.fee R simple t d.clock d.inverse C cp

include simple in
theorem original (n cost a p desired:ℕ)(debt ext raw w:Degree)(C:ℝ)(cp:0 ≤ C)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(e:ℝ)(ep:0<e)
    (order:desired+ext.pole ≤ p)(reserve:desired+1+debt.pole*n+2 ≤ p)
    (columns:∀ᶠ i:ℕ in atTop,(R.family.path.levels.params i).columns ≤ H i):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    R.family.S.a (b+1)/R.family.S.a (b+1+L) ≤ (H (b+1))^cost →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(d:V→ℕ)(Y:∀v,R.family.label (d v))(site:V→Site (R.family.side N per))
    {T I:ℕ→Type}[∀i,Countable (I i)]{o:∀i,V→Site (R.family.side i per)}
    (bank:∀i,Lamps (T i) (I i) G (Ψ i).p (o i) marks)(test:∀i,T i)
    {wK:V→ℝ}{αK CK:ℝ},(∀v,0<wK v) → 0 ≤ αK →
    Gross (bank (b+1+L)) wK (Ψ (b+1+L)).p.B αK CK →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (printed marks (Ψ (b+j.val+1+1)) (bank _) (test _))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),WilsonOriginalMountedFailedHalo.board R N per (b+1) W →
    ∀{d₀:ℕ}{frame:Frame G d₀}(section_:SectionData frame)(group:Hol G)
    (F:∀j:Fin L,WilsonOriginalMountedRegular.Filing R (Ψ (b+j.val+1)) (P j) (printed marks (Ψ (b+j.val+1)) (bank _) (test _)) s),
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega)
      (gust R.family.path N per N (microscopic R marks (Ψ N) d Y site) (b+1+L) live-printed marks (Ψ (b+1+L)) (bank _) (test _)) s
    let g:=regulatorRun R.family N per (b+1)
    let q:=desired+1+debt.pole*n
    (∀j,Poly.toll (S j) s ≤ pound R ext C N per (b+j.val+1+1) (b+j.val+1)) → (∀j,(F j).M ≤ pound R debt C N per (b+j.val+1+1) (b+j.val+1)) →
    (∀j:Fin L,(R.family.path.levels.budget (b+j.val+1)).supportExponent ≤ 100) →
    (∀j,1 ≤ (F j).α ∧ (F j).h=WilsonOriginalMountedRegularFare.crop (q+1+w.pole+raw.pole) g) →
    (∀j,(F j).W ≤ pound R w C N per (b+j.val+1+1) (b+j.val+1) ∧ (F j).gross ≤ pound R raw C N per (b+j.val+1+1) (b+j.val+1) ∧ (F j).rent ≤ C*(regulatorRun R.family N per (b+j.val+1+1))^(q+1+w.pole+1) ∧ (F j).δ ≤ C*(regulatorRun R.family N per (b+j.val+1+1))^(q+1+1)) →
    ‖read R N per W (show b+1 ≤ N by omega) (microscopic R marks (Ψ N) d Y site) s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(printed marks (Ψ (b+1)) (bank _) (test _) W).part s‖ ≤
      ‖enter‖+((4*(cost:ℝ)/Real.log 3)*WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+e*(shards marks s).card)*g^desired:=by
  obtain ⟨first,heard⟩:=WilsonOriginalPhysicalFieldsAtBoard.original R simple marks n cost a p desired debt.pole ext.pole raw.pole w.pole
    np load e ep order reserve columns
  let q:=desired+1+debt.pole*n
  have charged:=(((((restored R simple ext C cp cost).and (restored R simple debt C cp cost)).and
    (restored R simple raw C cp cost)).and (restored R simple w C cp cost)).and
    (WilsonOriginalOpticalCouplingFares.gain R simple cost (q+1+w.pole) C cp)).and
    (WilsonOriginalOpticalCouplingFares.gain R simple cost (q+1) C cp)
  obtain ⟨second,purchase⟩:=eventually_atTop.mp charged
  refine ⟨max first second,?_⟩
  intro b N per m k L aged mb live ratio way D Q π Γ Ψ course ticket d Y site T I _ o bank test wK αK CK wp width sold
    rows sourced s S sp wages W board dim frame section_ group F _ _ _ toll gross fixed crop terms
  obtain ⟨⟨⟨⟨⟨ticketPaid,inputs⟩,out⟩,widthPaid⟩,old⟩,diff⟩:=purchase (b+1) (by omega)
  apply heard b N per m k L (by omega) mb live ratio way D Q π Γ Ψ course ticket d Y site bank test wp width sold
    rows sourced s S sp wages W board section_ group F
  · intro j
    exact (toll j).trans (ticketPaid (i:=b+j.val+1+1) (j:=b+j.val+1) (by omega) (by omega) (by omega) (by omega) live ratio)
  · intro j
    exact (gross j).trans (inputs (i:=b+j.val+1+1) (j:=b+j.val+1) (by omega) (by omega) (by omega) (by omega) live ratio)
  · exact fixed
  · exact crop
  · intro j
    obtain ⟨window,mass,rev,err⟩:=terms j
    exact ⟨window.trans (widthPaid (i:=b+j.val+1+1) (j:=b+j.val+1) (by omega) (by omega) (by omega) (by omega) live ratio),
      mass.trans (out (i:=b+j.val+1+1) (j:=b+j.val+1) (by omega) (by omega) (by omega) (by omega) live ratio),
      rev.trans (old (per:=per) (i:=b+j.val+1+1) (by omega) (by omega) live ratio),
      err.trans (diff (per:=per) (i:=b+j.val+1+1) (by omega) (by omega) live ratio)⟩

end YM.Integration.WilsonOriginalDatedFieldsAtBoard
end
