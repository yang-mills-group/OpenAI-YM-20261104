import YM.Integration.WilsonPhysicalNodalChronology
import YM.Integration.WilsonMovingForkChronologicalCollar

/-! The total interior numerical bill for the filed physical pin uses its
actual finite marked programme on each date of the two-stop telescope. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalCollar
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat
open Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity QuadraticLocal.Sunrise Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus RegulatorIR.FVAAlt2 Source Labels
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses)
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkPrintedFile (Program row allSlots)
open WilsonMovingForkChronologicalTable (density)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonReceivedChronologicalDualInterval (Owned)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open scoped Topology Classical BigOperators

private def days (v K:ℕ):Finset ℕ:=(Ico v K).image Nat.pred

private theorem window {v K:ℕ}(vp:0 < v){j:ℕ}(hj:j∈days v K):v ≤ j+1 ∧ j+1 < K:=by
  obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
  obtain ⟨lo,high⟩:=mem_Ico.mp hi
  simp only [Nat.pred_eq_sub_one]
  omega

private theorem enumerate {v K:ℕ}(vp:0 < v)(f:ℕ→ℝ):
    ∑j∈days v K,f (j+1)=∑i∈Ico v K,f i:=by
  unfold days
  rw [sum_image]
  · apply sum_congr rfl
    intro i hi
    have:=mem_Ico.mp hi
    congr 1
    simp only [Nat.pred_eq_sub_one]
    omega
  · intro i hi j hj same
    have:=mem_Ico.mp hi
    have:=mem_Ico.mp hj
    simp only [Nat.pred_eq_sub_one] at same
    omega

private theorem divide {v c K:ℕ}(vc:v ≤ c)(ck:c ≤ K)(hi lo:ℕ→ℝ):
    (∑j∈Ico c K,hi j)+(∑j∈Ico v c,lo j)=∑j∈Ico v K,if c ≤ j then hi j else lo j:=by
  rw [←sum_Ico_consecutive (fun j=>if c ≤ j then hi j else lo j) vc ck,add_comm]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro j hj
    rw [if_neg (not_le_of_gt (mem_Ico.mp hj).2)]
  · apply sum_congr rfl
    intro j hj
    rw [if_pos (mem_Ico.mp hj).1]

variable {G:Gauge}(R:Run G)(simple:G.Simple){m k:ℕ}(hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin){φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books)

theorem original (cost n:ℕ):∃start:ℕ,∀{N per v L u c site:ℕ},0 < v → start ≤ v →
  ∀ (uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ v+L)(_kn:v+L ≤ N)(sk:site ≤ v+L),
  R.family.S.a v/R.family.S.a (v+L) ≤ (R.family.path.levels.clock.hatBeta v)^cost →
  ∀ (W:Initialize G)(d:Fin n→ℕ)(file:Filed R d (v+L))(Y:∀i,R.family.label (d i))
    (prog:Program R d (v+L))(addr:Fin n→ Cover)(node:Sample n)(q p size:ℕ)(η:ℝ)(Ψ:∀i,Rep G (R.family.side i per)),
  let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) Y
  let pin:=seats (R:=R) sk per addr
  let M:=row prog N per w pin
  let Λ (i:ℕ):=numerator R N per i (M i)
  0 ≤ η → (∀i,wrap (R.family.side (v+L) per) (node.layout i)=pin i) →
  (∀i,v ≤ i → i ≤ v+L → Mounted prog N per w pin i) →
  (∀j,v ≤ j+1 → j+1 < v+L → Owned (N:=N) R simple hk D Q π Γ Ψ books ahead
    (density prog N per w pin) j u v (allSlots n) (p+1) size η) →
  ‖signed R W d (N:=N) (per:=per) file Y (uv.trans (vc.trans ck)) node q‖  ≤ 
  (4*(cost:ℝ)/Real.log 3)*(WilsonOriginalOrdinaryFaceOrder.constant (allSlots n) (allSlots n).val.card+
    η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare (allSlots n) size)*(regulatorRun R.family N per v)^p+
  ‖reading R (N:=N) (Λ c) u (uv.trans vc)-reading R (N:=N) (Λ c) v vc‖+
  ‖reading R (N:=N) (Λ v) v le_rfl-evaluated q (regulatorRun R.family N per (v+L))
    (board R W d (vector R d (N:=N) (per:=per) file Y) node univ)‖:=by
  obtain ⟨start,fees⟩:=WilsonMovingForkChronologicalCollar.original R simple hk D Q π Γ books ahead cost n
  refine ⟨start,?_⟩
  intro N per v L u c site vp past uv vc ck kn sk radius W d file Y prog addr node q p size η Ψ w pin M Λ ep sits minted each
  let hi:=fun j=>‖feeAt R N per u M j‖
  let lo:=fun j=>‖feeAt R N per v M j‖
  let bill:=WilsonPhysicalNodalChronology.expenses R W d file Y prog addr node sk uv vc ck kn sits minted q
    hi lo _ _ (fun _ _=>le_rfl) le_rfl (fun _ _=>le_rfl) le_rfl
  let stop:=fun j=>if c ≤ j+1 then u else v
  have total:=fees past kn radius d prog w pin Ψ u p size η ep (days v (v+L))
    (fun j h=>(window vp h).1) (fun j h=>(window vp h).2)
    (fun j h=>⟨minted _ (window vp h).1 (window vp h).2.le,
       minted _ ((window vp h).1.trans (Nat.le_succ _)) (by have:= (window vp h).2;omega)⟩)
    (fun j h=>each j (window vp h).1 (window vp h).2) stop
    (fun j _=>by dsimp [stop];split <;> simp [uv])
  have route (j:ℕ): ‖feeAt R N per (stop j) M (j+1)‖=(if c ≤ j+1 then hi (j+1) else lo (j+1)):=by
    dsimp [stop,hi,lo]
    split <;> rfl
  change (∑j∈days v (v+L),‖feeAt R N per (stop j) M (j+1)‖)  ≤  _ at total
  simp_rw [route] at total
  rw [enumerate vp (fun j=>if c ≤ j then hi j else lo j),←divide vc ck hi lo] at total
  linarith only [total,bill]

end YM.Integration.WilsonPhysicalNodalCollar
end

