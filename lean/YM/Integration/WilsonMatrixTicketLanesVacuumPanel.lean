import YM.Integration.WilsonMatrixTicketLanesVacuumIncome
import YM.Integration.WilsonMatrixTicketLanesRegisteredTilt

/-! The two earlier returns and the complete signed first variation at the
original finite spatial wave. Physical input, spectator and vacuum centers
stay inside the same probability on every term of the genuine spatial sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumPanel
open Filter Function MeasureTheory Finset Set Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing WilsonMatrixTicketLanesRegisteredHearing
open WilsonInheritedRegisteredField
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {k N per:ℕ}
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "lower" => Config G (R.family.side k per)
local notation "Ω" => (lower × upper)
local notation "Sites" => (Fin 2 → Site (R.family.side N per))
local notation "Re" => Complex.reCLM
local notation "Im" => Complex.imCLM

inductive Kind where
  | previousCovariance
  | previousCumulant
  | all

def entry (kind:Kind) (live:k<N) (a b w:readings Ω):ℝ:=
  let E:=earlier R (p:=per) live
  let I:=conditional R (p:=per) live
  match kind with
  | .previousCovariance=>covariance E (I w) (covariance I a b)
  | .previousCumulant=>cubic E (I w) (I a) (I b)
  | .all=>receipts R live a b w

def signed (kind:Kind) (live:k<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4)
    (φ:Test 2) (χ:ℂ →L[ℝ]ℝ) (w:Sites → readings Ω):ℝ:=
  panel R live birth v φ χ fun x a b=>entry R kind live a b (w x)

private theorem phase (χ:ℂ →L[ℝ]ℝ) (sel:χ=Re ∨ χ=Im) (z:ℂ):|χ z|≤‖z‖:=by
  rcases sel with rfl|rfl
  · exact Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z

theorem tested (kind:Kind) (live:k<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4)
    (φ:Test 2) (χ:ℂ →L[ℝ]ℝ) (sel:χ=Re ∨ χ=Im) (w:Sites → readings Ω) {A B M:ℝ}
    (an:0≤A) (bn:0≤B)
    (fa:∀o U,‖regular (C:=R.family) (per:=per) R.makes live (v 0) o U‖≤A)
    (fb:∀o U,‖regular (C:=R.family) (per:=per) R.makes live (v 1) o U‖≤B)
    (source:∀x,joint R live (WilsonMatrixTicketLanesVacuumIncome.absolute (w x))≤M):
    |signed R kind live birth v φ χ w|≤
      (24*(A*B)*M)*(∑x:Sites,‖WilsonExternalMeshMass.charge R.family φ x‖):=by
  let weight:=fun x:Sites=>WilsonExternalMeshMass.charge R.family φ x
  let D:=6*(A*B)*M
  have bound (x:Sites) (η θ:ℂ →L[ℝ]ℝ) (hη:η=Re ∨ η=Im) (hθ:θ=Re ∨ θ=Im):
      |entry R kind live (filed R live birth (v 0) ((R.family.S.toDepth live per).parent (x 0)) η)
        (filed R live birth (v 1) ((R.family.S.toDepth live per).parent (x 1)) θ) (w x)|≤D:=by
    let a:=filed R live birth (v 0) ((R.family.S.toDepth live per).parent (x 0)) η
    let b:=filed R live birth (v 1) ((R.family.S.toDepth live per).parent (x 1)) θ
    have ea(q:Ω):|a.val q|≤A:=(phase η hη _).trans (fa _ q.2)
    have eb(q:Ω):|b.val q|≤B:=(phase θ hθ _).trans (fb _ q.2)
    have estates:=WilsonMatrixTicketLanesVacuumIncome.original R live a b (w x) an bn ea eb
    have held:=source x
    have next:=mul_le_mul_of_nonneg_left held (show 0≤6*(A*B) by positivity)
    cases kind with
    | previousCovariance=>
      refine estates.1.trans (le_trans ?_ next)
      have m0:0≤joint R live (WilsonMatrixTicketLanesVacuumIncome.absolute (w x)):=by
        change 0≤∫V:lower,∫U:upper,|(w x).val (V,U)| ∂ActualWilsonConditionalRoots.fibre R.family (N:=N) V ∂scene R.family.path N per k
        exact integral_nonneg (fun _=>integral_nonneg (fun _=>abs_nonneg _))
      gcongr
      norm_num
    | previousCumulant=>exact estates.2.1.trans next
    | all=>exact estates.2.2.trans next
  have bank (x:Sites):
      let op:=fun η θ=>entry R kind live (filed R live birth (v 0) ((R.family.S.toDepth live per).parent (x 0)) η)
        (filed R live birth (v 1) ((R.family.S.toDepth live per).parent (x 1)) θ) (w x)
      |channel χ (weight x) op|≤(24*(A*B)*M)*‖weight x‖:=by
    intro op
    have rr:=bound x Re Re (Or.inl rfl) (Or.inl rfl)
    have ii:=bound x Im Im (Or.inr rfl) (Or.inr rfl)
    have ri:=bound x Re Im (Or.inl rfl) (Or.inr rfl)
    have ir:=bound x Im Re (Or.inr rfl) (Or.inl rfl)
    have a:|op Re Re-op Im Im|≤2*D:=(abs_sub _ _).trans (by change _≤2*D;linarith only [rr,ii])
    have b:|op Re Im+op Im Re|≤2*D:=(abs_add_le _ _).trans (by change _≤2*D;linarith only [ri,ir])
    have wi:|χ (weight x*Complex.I)|≤‖weight x‖:=(phase χ sel _).trans_eq (by rw [norm_mul,Complex.norm_I,mul_one])
    have p:=mul_le_mul (phase χ sel (weight x)) a (abs_nonneg _) (norm_nonneg _)
    have q:=mul_le_mul wi b (abs_nonneg _) (norm_nonneg _)
    unfold channel
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    calc
      _≤‖weight x‖*(2*D)+‖weight x‖*(2*D):=add_le_add p q
      _=_:=by dsimp [D];ring
  unfold signed panel
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _=>bank x

end YM.Integration.WilsonMatrixTicketLanesVacuumPanel
