import YM.Integration.WilsonMovingForkChronologicalSale
import YM.Integration.WilsonOriginalTwoFlatCompact

/-! Two original flat readings of the very same dated physical-pin print.
Its binder sites may occupy any of the positions paid in the capture house. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalCapturedWord
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
open Push Push.Local Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Affinity
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato WilsonRootedKioskOccupiedSlip WilsonOlderFreshGraphSlate
open WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows Pert.Asymptotics
open WilsonMovingForkPrintedFile (Program row parent allSlots)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple){n N per c u v K:ℕ}{d:Fin n → ℕ}
  (prog:Program R d K)(w:∀a,R.family.label (d a))(pins:Fin n → Site (R.family.side K per))
local notation "C" => R.family
local notation "rep" => (C).path.rep N per c

theorem original (ck:c < K)(kn:K ≤ N)(cu:(C).ref 0 ≤ u)(uv:u ≤ v)(vc:v ≤ c)
    (first:WilsonCenteredCaptureClock.first R simple ≤ c)(ou:Opened C 0 u per)(ov:Opened C 0 v per)
    (Z:Support ((C).side c per))(center:0∈Z)(house:∀a,parent R ck.le per pins a∈Z)
    (rad:ℕ)(near:∀a,separation (parent R ck.le per pins a) 0 ≤ rad) :
    let b:=prog N per w pins c ck
    let g:=regulatorRun (C) N per c
    let s:=allSlots n
    let M:=numerator R N per c (row prog N per w pins c)
    ∀{ord seats shelf ext:ℕ}{stripU slack gross:ℝ},
      0 ≤ b.strip → b.order ≤ ord → 1 ≤ seats → n ≤ seats → (∑a,b.load a) ≤ shelf →
      Invoice.Supports (rep).p stripU ((rep).p.supportExponent+2) g b.strip slack →
      Invoice.price (rep).p stripU (ord+shelf+1) seats ((rep).p.supportExponent+2) slack G ≤
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2 →
      (∑a:b.index,Real.exp (b.strip*(b.binder a).length)*WilsonIndependentCollarSlateIntensity.amount
        (b.copies a) (b.binder a).center) ≤ gross*(3*g⁻¹)^ext →
      let maxCost:=((2:ℝ)^(ord+shelf+1))^2 * max 1 gross*(3*g⁻¹)^((∑a,b.load a)+1+2+ext)
      ∃C₀ C₁:ℝ,0 ≤ C₀ ∧ 0 ≤ C₁ ∧ C₀ ≤ maxCost ∧ C₁ ≤ maxCost ∧
        let earn:=WilsonPlantedOrdinary.fare (rep).p Z (fun _:Fin n=>1) C₀ C₁ rad
          ((C).localSection 0) (C).params (price G (max (rep).p.order (rep).p.power))
          (R.alloy.B.a.clock.forcedAllowance c) (LocalComparison.forcedDivisor (C) c) s
        ‖reading R (N:=N) M u (uv.trans vc)-reading R (N:=N) M v vc‖ ≤
          2*capital (C) c earn 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8):=by
  intro b g s M ord seats shelf ext stripU slack gross hs dep oc slots fit fund fare wage maxCost
  obtain ⟨equal,C₀,C₁,p₀,p₁,c₀,c₁,rent,full⟩:=WilsonOriginalTwoFlatIRMounted.original
    b.binder b.load b.copies hs dep oc (by simpa using slots) fit (rep).p fund fare wage
  refine ⟨C₀,C₁,p₀,p₁,c₀,c₁,?_⟩
  have paid:=WilsonOriginalTwoFlatCompact.original R simple cu uv vc (ck.trans_le kn) ou ov first
    _ rfl b.wallet s Z center (fun a _=>house a) rad (fun a _=>near a)
    (fun _:Fin n=>1) (fun _=>zero_lt_one) rent full
  let lamps:=rendered (mounted b.binder (fun i:b.index=>(b.copies i).rows
    (WilsonOlderFreshGraphPointWallet.point (b.binder i).center) disk)) (rep).p g
  have named: M=(fun U=>((rep).eval U:ℂ)*(Poly.pass (bare lamps b.wallet U)).part s):=by
    funext U
    simpa only [M,numerator,row,dif_pos ck,b,g] using
      congrArg (fun P=>((rep).eval U:ℂ)*(Poly.part P s)) (equal b.wallet U).symm
  rw [named]
  exact paid

end YM.Integration.WilsonPhysicalNodalCapturedWord
end
