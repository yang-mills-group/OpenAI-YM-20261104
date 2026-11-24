import YM.Integration.WilsonTrueProjectedDualAppointment
import YM.Integration.WilsonTrueProjectedCourse

/-! The hard numerator is returned on its issuing course. The canonical
null numerator and that remaining hard account have one combined budget
over every date, with the physical upper boundary retained. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedDualHistory
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonTrueProjectedColumnDescent
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) {d m N p k : ℕ}
local notation "𝓒" => R.family
local notation "σ" => (R.family.labels.level d).coeffSize
local notation "Q" => GermGraph.store R.family d p
local notation "V" => GermGraph.value (C:=R.family) d N p
local notation "Y" => GermGraph.calValues (C:=R.family) d N p
local notation "π" => GermGraph.page (C:=R.family) d p
local notation "X" => GermGraph.measuring R.family d N p
local notation "U" => GermGraph.transition (C:=R.family) d N p
local notation "S" => R.family.localSection d
local notation "κ" => safety R.family
abbrev Spaces (R : Run G) (p : ℕ) := ∀ j, Config G (R.family.side j p) → ℂ
variable (Ψ : ∀ j, RG.Rep G (R.family.side j p))

def Admitted (j : ℕ) (h : Q j) (amount : ℝ) : Prop :=
  h.Format 0 (𝓒).params (Ψ j) ∧ h.remBound 0 (Ψ j) (κ j) amount

def Signed (F : Spaces R p) (j : ℕ) (price : ℝ) : Prop :=
  ∃ e : Q j, Admitted R Ψ j e price ∧ σ e.x ≤ price ∧
    U j (F (j+1)) = F j + e.density 0 S (Ψ j)

def HardReturn (j : ℕ) (spare : ℝ) : Prop :=
  ∀ (h : Q (j+1)) (B : ℝ), Admitted R Ψ (j+1) h B →
    ∃ (z : Q j) (u : ℝ), Admitted R Ψ j z u ∧ σ z.x ≤ u ∧
      U j (account h (Ψ (j+1))) = z.density 0 S (Ψ j) ∧
      (2+4*stock (𝓒) j)*u ≤ decay (𝓒) j*B + spare

def Full (F : Spaces R p) (j : ℕ) (v : (𝓒).label d) (total : ℝ) : Prop :=
  ∃ (q h : Q j) (r B : ℝ), reads d N p j q r ∧ π j q=0 ∧ Admitted R Ψ j h B ∧
    r+B ≤ total ∧ V j q + account h (Ψ j) = Y j v - F j

def localBill (price spare : ℕ → ℝ) (j : ℕ) := (2+4*stock (𝓒) j)*price j + spare j

theorem history (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    {first stop : ℕ} (range : m ≤ first) (top : stop ≤ N) {γ ε : ℝ}
    (F : Spaces R p) (template : ∀ j, Q j) (price spare : ℕ → ℝ)
    (opened : ∀ i ≥ first, i < stop → Opened (𝓒) d i p)
    (gate : ∀ i ≥ first, i < stop → Gate (𝓒) d N p i γ ε)
    (model : ∀ i ≥ first, i < stop → F i =ᶠ[𝓝 1] V i (template i) ∧
      ∃ W, reads d N p i (template i) W)
    (fresh : ∀ i ≥ first, i < stop → Signed R (d:=d) (N:=N) Ψ F i (price i))
    (hard : ∀ i ≥ first, i < stop → HardReturn R (d:=d) (N:=N) Ψ i (spare i))
    (boundary : ℝ) (initial : ∃ v, Full R (d:=d) (N:=N) Ψ F stop v boundary) :
    ∀ i ≥ first, i ≤ stop → ∃ v,
      Full R (d:=d) (N:=N) Ψ F i v (wallet (𝓒) (localBill R price spare) boundary (stop-i) i) ∧
      (i < stop → X i v = π i (template i)) := by
  intro i fi is
  induction is using Nat.decreasingInduction with
  | self =>
    obtain ⟨v,hv⟩ := initial
    exact ⟨v,by simpa [wallet] using hv,by omega⟩
  | of_succ i ib ih =>
    obtain ⟨y,⟨q,h,r,B,paid,pn,hpaid,total,input⟩,_⟩ := ih (by omega)
    obtain ⟨e,epaid,ex,fstep⟩ := fresh i fi ib
    obtain ⟨z,u,zpaid,zx,hstep,power⟩ := hard i fi ib h B hpaid
    obtain ⟨near,W,base⟩ := model i fi ib
    have hi := opened i fi ib
    have late : i < N := ib.trans_le top
    let fit := fitting d N p i R.makes hi late.le
    let v := fit.symm (π i (template i))
    obtain ⟨fmt,fee,next,_,npaid,nn,_,_,out⟩ := WilsonTrueProjectedDualAppointment.original
      R π₀ Γ Ψ course (range.trans fi) late hi (gate i fi ib) y q h e z (template i)
      (F (i+1)) (F i) paid pn hpaid ⟨epaid.1,epaid.2,ex⟩ ⟨zpaid.1,zpaid.2,zx⟩ near base
      (by rw [input]; abel) fstep hstep
    refine ⟨v,⟨next,beside e z,_,_,npaid,nn,⟨fmt,fee⟩,?_,out⟩,?_⟩
    · have nonnegative : 0 ≤ decay (𝓒) i :=
        Real.rpow_nonneg (zero_le_one.trans (factor_positive (𝓒) i).le) _
      have bill := mul_le_mul_of_nonneg_left total nonnegative
      have dx : stop-i = (stop-(i+1))+1 := by omega
      rw [dx,wallet]
      change decay (𝓒) i*r+(1+4*stock (𝓒) i)*(price i+u)+(price i+u) ≤ _
      calc
        _ = (decay (𝓒) i*r+(2+4*stock (𝓒) i)*price i)+(2+4*stock (𝓒) i)*u := by ring
        _ ≤ (decay (𝓒) i*r+(2+4*stock (𝓒) i)*price i)+(decay (𝓒) i*B+spare i) :=
          add_le_add le_rfl power
        _ = decay (𝓒) i*(r+B)+localBill R price spare i := by unfold localBill; ring
        _ ≤ _ := add_le_add bill le_rfl
    · intro _
      exact fit.apply_symm_apply _

end YM.Integration.WilsonTrueProjectedDualHistory
