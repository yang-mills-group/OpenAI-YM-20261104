import YM.Integration.WilsonReceivedCompactQUnitReadout
import YM.Integration.WilsonOriginalNullProjectedPrice
import YM.Integration.WilsonMeasuredSignedEnvelope
import YM.Integration.WilsonMeasuredOwnerIntegrable

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedQUnitCompulsory
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
open Filter MergeProof.Accent RG3.Law OPE.Therm Extra.Trajectories Extra.Histories Trace.Physical.GermGraph
variable {G:Gauge} (R:Run G) {N per:ℕ}
local notation "C₀" => R.family
local notation "H₀" => R.family.path

theorem add {u t:ℕ} (age:u ≤ t) (f h:Config G (R.family.side t per) → ℂ)
    (hf:Integrable (fun U=>(R.family.path.rep N per t).eval U • f U) (prior G _))
    (hh:Integrable (fun U=>(R.family.path.rep N per t).eval U • h U) (prior G _)) :
    actualTransport (C₀) (N:=N) (f+h) age=actualTransport (C₀) (N:=N) f age+actualTransport (C₀) (N:=N) h age := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le age
  let F:=fun U=>(R.family.path.rep N per (u+d)).eval U • f U
  let H:=fun U=>(R.family.path.rep N per (u+d)).eval U • h U
  have whole:(fun U=>(R.family.path.rep N per (u+d)).eval U • ((f+h) U))=F+H := by
    funext U;exact smul_add _ _ _
  have together:= (WilsonReceivedQUnitPosterior.raw (N:=N) R u d (F+H)).symm.trans
    ((WilsonOriginalNullCorridor.flow_add (C₀) 0 N per u d F H hf hh).trans
      (congrArg₂ (·+·) (WilsonReceivedQUnitPosterior.raw (N:=N) R u d F) (WilsonReceivedQUnitPosterior.raw (N:=N) R u d H)))
  funext V
  unfold actualTransport
  rw [whole,together]
  exact smul_add _ _ _

def onset (simple:G.Simple) :ℕ := (eventually_atTop.mp (WilsonOriginalNullProjectedPrice.original R 0 simple)).choose

variable {m k b:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "W" => Ψ b
local notation "realW" => R.family.path.rep N per b
local notation "hard₀" h:max => WilsonMeasuredCoefficientTransport.account h W

include course in
theorem row (simple:G.Simple) (booked:onset R simple ≤ b) (start:m ≤ b) (live:b ≤ N)
    (o:Site (R.family.side b per)) (h:Coefficient (F₀) (R.family.side b per)) {B:ℝ}
    (shaped:h.Format o R.family.params W) (paid:h.remBound o W (LocalComparison.forcedDivisor R.family b) B)
    (zero:projection (F₀) R.family.params (W).p.threshold o h=0) :
    Integrable (h.density o (S₀) W) (prior G _) ∧ Integrable (hard₀ h) (prior G _) ∧
      ∀U,‖((W).eval U)⁻¹ • (h.density o (S₀) W U-(hard₀ h) U)‖ ≤ 2*B := by
  have stock:=(course.1.walk b start live).truep
  have pack:=(eventually_atTop.mp (WilsonOriginalNullProjectedPrice.original R 0 simple)).choose_spec b booked
    per W stock.point o h shaped paid (Nat.zero_le _) (Nat.zero_le _)
  have price:‖h.x 0‖ ≤ B := by
    have v:=pack.1
    rw [zero,zero_sub,WilsonOriginalNullUnitFlow.size] at v
    simpa using v
  have debt:=WilsonMeasuredSignedEnvelope.original R simple π Γ Ψ course start live o h shaped paid
     (h.density o (S₀) W) (fun _=>0) (fun _=>by simp)
  refine ⟨(h.envelope (S₀) stock.valid paid shaped).integrableC _,WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course start live (S₀) R.family.params o h shaped paid,?_⟩
  intro U
  have eq:((W).eval U)⁻¹ • (h.density o (S₀) W U-(hard₀ h) U)=
      h.density o (S₀) W U/((W).eval U:ℂ) - (fun _ : Config G (R.family.side b per)=> (0:ℂ)) U -(hard₀ h) U/((W).eval U:ℂ) := by
    rw [Complex.real_smul,Complex.ofReal_inv];simp only [div_eq_mul_inv,sub_zero];ring
  rw [eq]
  exact (debt.2 U).trans (by linarith only [price])

def Heard (n:ℕ) (f:Config G (R.family.side (b+n) per) → ℂ) (forced:Config G (R.family.side b per) → ℂ)
    (z:ℂ) (B:ℝ) : Prop := ∀u (age:u ≤ b) (V:Config G (R.family.side u per)),
  ‖actualTransport (C₀) (N:=N) (fun U=>((Ψ (b+n)).eval U)⁻¹ • f U) (age.trans (Nat.le_add_right b n)) V -
    actualTransport (C₀) (N:=N) (fun U=>((W).eval U)⁻¹ • forced U) age V - z‖ ≤ B

include course in
theorem terminal (n:ℕ) (start:m ≤ b) (live:b+n ≤ N)
    (f:Config G (R.family.side (b+n) per) → ℂ) (d hard:Config G (R.family.side b per) → ℂ) (z:ℂ) {B:ℝ}
    (heard:WilsonReceivedQUnitPosterior.Viewed (N:=N) R Ψ b n f d z)
    (entry:Integrable d (prior G _)) (honest:Integrable hard (prior G _))
    (price:∀U,‖((W).eval U)⁻¹ • (d U-hard U)‖ ≤ B) :Heard (N:=N) R Ψ n f hard z B := by
  let soft:=fun U=>((W).eval U)⁻¹ • (d U-hard U)
  let fee:=fun U=>((W).eval U)⁻¹ • hard U
  have hb:b ≤ N:=by omega
  have payout:(W).eval=(realW).eval:=(course.1.walk b start hb).view
  have cancel (a:Config G (R.family.side b per) → ℂ):(fun U=>(realW).eval U • (((W).eval U)⁻¹ • a U))=a := by
    funext U
    have nv:(realW).eval U≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson hb U).ne'
    rw [payout,smul_smul,mul_inv_cancel₀ nv,one_smul]
  have wf:Integrable (fun U=>(realW).eval U • fee U) (prior G _):=(cancel hard).symm ▸ honest
  have ws:Integrable (fun U=>(realW).eval U • soft U) (prior G _):=(cancel (d-hard)).symm ▸ entry.sub honest
  have wc:Integrable (fun U=>(realW).eval U • z) (prior G _) := by
    simpa only [Complex.real_smul,liftVac] using (vac_integrable (H₀) N per b R.makes.wilson hb).mul_const z
  have wsf:Integrable (fun U=>(realW).eval U • (soft+fee) U) (prior G _) := by
    simp only [Pi.add_apply,smul_add];exact ws.add wf
  have group:(fun U=>((W).eval U)⁻¹ • d U + z)=(soft+fee+(fun _=>z)) := by
    funext U;simp only [Pi.add_apply,soft,fee,smul_sub,sub_add_cancel]
  intro u age V
  have first:=congrFun (heard.1 u age) V
  rw [group,add R age (soft+fee) (fun _=>z) wsf wc,add R age soft fee ws wf,Pi.add_apply,Pi.add_apply,
    actualTransport_const (C₀) R.makes hb z age V] at first
  have eq:actualTransport (C₀) (N:=N) (fun U=>((Ψ (b+n)).eval U)⁻¹ • f U) (age.trans (Nat.le_add_right b n)) V -
     actualTransport (C₀) (N:=N) fee age V-z=actualTransport (C₀) (N:=N) soft age V := by rw [first];abel
  change ‖_ - actualTransport (C₀) (N:=N) fee age V - z‖ ≤ B
  rw [eq]
  exact actualTransport_norm_le (C₀) R.makes hb price age V

end YM.Integration.WilsonReceivedQUnitCompulsory
