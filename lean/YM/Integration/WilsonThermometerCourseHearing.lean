import YM.Integration.WilsonReceivedPostLog
import YM.Integration.WilsonThermometerCourseIntake
import YM.Integration.WilsonLocalCompactRichPortUnits

/-! Physical and finite conditional thermometer coefficients at the true upper coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCourseHearing
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

local notation "I" => Fin 3
local notation "J" => Stock.census (Fin 3)
def disks (_ : Fin 3) : Set ℂ := {a | ‖a‖ ≤ 1}
def sectors (_ : Fin 3) : Submodule ℝ ℂ := ⊥
def fired : Wallet disks := fun _ => ⟨1,by simp [disks]⟩

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {m N per k i : ℕ} (live : i < N) (o : Positions (Fin 3) (R.family.side N per))

def offered (x : Wallet disks) (U : Config G (R.family.side (i+1) per)) : Poly J :=
  Poly.inject (fun s => (∏ v ∈ s.val, (x v).val) * (incoming R A simple live o U).part s)

/-- Deleting an input by setting its scalar to zero deletes every Wilson numerator
which contains that input, on the same held group field and complete old vacuum. -/
theorem offered_tests (s : (J).Mode) (U : Config G (R.family.side (i+1) per)) :
    Attn sectors disks s.val (fun x => (offered R A simple live o x U).part s) := by
  let c := (incoming R A simple live o U).part s
  change Attn sectors disks s.val (fun x => (∏ v ∈ s.val,(x v).val)*c)
  refine ⟨?_,?_,?_⟩
  · intro x y keep
    exact congrArg (fun z => z*c) (Finset.prod_congr rfl fun j hj => congrArg Subtype.val (keep j hj))
  · intro j hj t x y z a b rel
    let k := (∏ v ∈ s.val.erase j,(t v).val)*c
    have updated (p : disks j) : (∏ v ∈ s.val,((Function.update t j p) v).val)*c=p.val*k := by
      rw [← Finset.mul_prod_erase _ _ hj,Function.update_self,mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun v hv => congrArg Subtype.val (Function.update_of_ne (Finset.ne_of_mem_erase hv) p t)
    rw [updated,updated,updated,rel]
    simp only [Complex.real_smul,add_mul]
    ring
  · intro j hj t h
    have zero : (t j).val=0 := (Submodule.mem_bot ℝ).mp h
    rw [← Finset.mul_prod_erase _ _ hj,zero,zero_mul,zero_mul]

theorem fired_input : offered R A simple live o fired = incoming R A simple live o := by
  funext U
  ext s
  simp [offered,Poly.part,Poly.inject,fired]

variable (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books) (order shelf seats : ℕ) (floor : m ≤ i)
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "gm" => Coat.gStep (R.family.path.rep N per m).beta
local notation "ages" => (fun u : Fin 3 => (grade u).val)
local notation "B" => R.family.path.levels.budget i
local notation "hatβ" => R.family.path.levels.clock.hatBeta i

/-- The course is attached to the literal seven-face history. Its force, model and rent
come from the same returned post. The source radii and incoming rent are restored once. -/
theorem original
    (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (actual : (Ψ i).eval = (R.family.path.rep N per i).eval)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay) (fit : k≤R.alloy.B.a.clock.J i)
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor (offered R A simple live o))
    (s : (J).Mode) (v : I) (hv : v ∈ s.val) (loss depth : ℕ)
    (deep : 2*((loss+2)+1)+8≤order) (aged : (loss+2)+4≤3*k+2)
    (H cap : ℝ) (cap₀ : 0≤cap) {ε : ℝ} (ep : 0<ε)
    (late : (eventually_atTop.mp (WilsonReceivedPaidCourse.original R simple D φ paid (ages)
      s v hv (loss+2) depth order shelf k seats deep aged H cap cap₀ ep)).choose ≤ i)
    (radius : (gs)^loss ≤ Poly.toll P.w s)
    (rent : (8*(budgetR R i)^seats)*P.rent ≤ ε*(gs)^(loss+2))
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)
    (b : Stationary.Link G (R.family.side i per)) :
    let angle := Stationary.arm G (R.family.side i per) 1 b
    ∀ z : ℝ, |z| ≤ |H| * (Real.log (hatβ))^depth*(((B).B:ℝ)^2*(B).threshold)/(gs) →
      (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
      let U := Integral.sample (gs) angle
      flags (Ψ i).p.threshold U = ∅ →
      let measured := Order.logTo 3 (((((R.family.path.rep N per i).eval U):ℂ)⁻¹) •
        incoming R A simple live.le o U)
      let bank := Air.craft P.model (fun a => (P.model a).paint fired) (ages) (π (i+1))
        (AllOrder.Floe.Step.tape (Burn.horizon k+2))
      let program := (RunFormalChain.fromRun R).step N i per live
      let finite := Order.value ((gs):ℂ) (Order.logMarked (Bulk.Fk program F tag bank angle order))
      (gm)^7 * ‖(measured-finite).part s‖ ≤ 8*ε*(gm)^9 := by
  intro angle z hz localCap U healthy measured bank program finite
  have sale := WilsonReceivedPostLog.original R hk D Q π Γ Ψ books ahead disks sectors (ages)
    order shelf seats i floor (offered R A simple live o) simple paid course law enrolled fund live fit
    P s v hv (loss+2) depth deep aged H cap cap₀ ep late fired F tag b z hz localCap healthy
  dsimp only at sale
  rw [fired_input,step,actual] at sale
  change ‖(measured-finite).part s‖ ≤ _ at sale
  have weight := Poly.worth P.salary.positive s
  have nonneg : 0≤gs := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have measuredPos : 0≤gm := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have band : (gs) ≤ 2*(gm) := WilsonLocalCompactRichPortUnits.compared R simple
    (floor.trans (Nat.le_succ i)) live per
  have budget : (8*(budgetR R i)^seats)*P.rent+ε*(gs)^(loss+2) ≤
      (2*ε*(gs)^2)*Poly.toll P.w s := calc
    _ ≤ ε*(gs)^(loss+2)+ε*(gs)^(loss+2) := add_le_add rent le_rfl
    _ = (2*ε*(gs)^2)*(gs)^loss := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left radius (by positivity)
  have error := sale.trans ((div_le_iff₀ weight).mpr budget)
  calc
    _ ≤ (gm)^7 * (2*ε*(gs)^2) := mul_le_mul_of_nonneg_left error (pow_nonneg measuredPos _)
    _ ≤ (gm)^7 * (2*ε*(2*(gm))^2) := by gcongr
    _ = _ := by ring

end YM.Integration.WilsonThermometerCourseHearing
end

