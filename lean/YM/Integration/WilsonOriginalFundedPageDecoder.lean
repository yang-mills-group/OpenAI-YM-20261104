import YM.Integration.WilsonOriginalBalancedTrialCoordinates
import YM.Integration.WilsonCapturedPrimaryWeakTrialEngineering

/-! The complete finite measured page for an arbitrary publicly admitted row.
Engineering, lower grades, native forced payment and the unit use one inverse. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFundedPageDecoder
open Function Finset Filter MeasureTheory Lattice RG Wilson Source Labels Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02 RG16 RG16.Literal
open Multi Extra.Multi WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonPositionProgramBlockedTrialNodes WilsonFirstReceivedRadialStencil
open WilsonOriginalMicroscopicGuardedReporters WilsonCapturedPrimaryWeakTrialRadial WilsonCapturedPrimaryWeakTrialNonconstant
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(h:ℕ)
local notation "Fr" => R.family.labels.level h
local notation "Sec" => R.family.localSection h

private theorem carry {i n L N per:ℕ}(eq:n=L)(hi:i+n≤N)(hl:i+L≤N)(v:R.family.label h):
    WilsonPositionProgramOriginalBlockedTrial.carried R h (b:=i) (n:=n) (p:=per) hi 0 v=
      WilsonPositionProgramOriginalBlockedTrial.carried R h (b:=i) (n:=L) (p:=per) hl 0 v:=by
  subst n
  rfl

def shortfall (N per i target:ℕ)(e:R.family.label h)(fare:ℝ):ℝ:=
  max 0 (fare/(regulatorRun R.family N per (i+1))^(grade target h 1)-originalRent R h i e)

def Earned {i L N per:ℕ}(target:ℕ)(live:i+L<N)(η:ℝ)(e:R.family.label h)
    (A:R.family.label h ≃ₗ[ℂ] R.family.label h)(Y:Config G (R.family.side i per) → ℂ)(fare:ℝ):Prop:=
    let v:=A.symm e
    let eng:=WilsonCapturedPrimaryWeakTrialEngineering.gain R h i L
    let P:=R.family.path.rep N per i
    let extra:=shortfall R h N per i target e (‖eng‖*fare)
    A v=e ∧
    (Fr).coeffSize v ≤ stretch R η i (i+L)*(Fr).coeffSize e ∧
    ∃q:Coefficient (Fr) (R.family.side i per),q.Format 0 R.family.params P ∧
    q.remBound 0 P (safety R.family i) (2*stock R.family i*(Fr).coeffSize e) ∧
    q.density 0 (Sec) P=WilsonPositionProgramOriginalBlockedTrial.carried R h (b:=i) (n:=L) (p:=per) live.le 0 v ∧
    projection (Fr) R.family.params P.p.threshold 0 q=e ∧
    ∀depth,h ≤ depth →
      let err:=gMap R.family N per h i (e-decode R h N per i target depth (fun W=>eng*Y W))
      (Fr).coeffSize err ≤ price R h N per i target depth e extra ∧
      ∀a,‖err a‖ ≤ price R h N per i target depth e extra

theorem original {i L N per:ℕ}(target:ℕ)(live:i+L<N)(η:ℝ)(e:R.family.label h)
    (A:R.family.label h ≃ₗ[ℂ] R.family.label h)
    (paid:Arrived R h i (i+L) N per target (Nat.le_add_right i L) live.le η A e)
    (Y:Config G (R.family.side i per) → ℂ)(fare:ℝ)
    (nodes:∀D,∀a∈tests (Fr),∀j ≤ D,
      let W:=field R h N per i target D a j
      ‖actualTransport R.family (N:=N)
        (fun U=>part (Sec) 0 (R.family.path.rep N per (i+L)) U (A.symm e)) (Nat.le_add_right i L) W-Y W‖ ≤ fare):
    Earned R h target live η e A Y fare:=by
  unfold Earned
  intro v eng P extra
  have span:=Nat.le_add_right i L
  have now:=span.trans_lt live
  obtain ⟨size,q,fmt,rem,word,proj,invoice⟩:=paid
  have issued:q.density 0 (Sec) P=WilsonPositionProgramOriginalBlockedTrial.carried R h (b:=i) (n:=L) (p:=per) live.le 0 v:=by
    exact word.trans (carry R h (show (i+L)-i=L by omega) _ _ v)
  have normed (W):reading (Sec) P 0 q W=eng*actualTransport R.family (N:=N)
    (fun U=>part (Sec) 0 (R.family.path.rep N per (i+L)) U v) span W:=by
    unfold reading
    rw [issued,div_eq_mul_inv,mul_comm]
    exact WilsonCapturedPrimaryWeakTrialEngineering.normalized R h N per i live.le 0 v W
  refine ⟨A.apply_symm_apply _,size,q,fmt,rem,issued,proj,?_⟩
  intro depth enough err
  have pg:0<(regulatorRun R.family N per (i+1))^(grade target h 1):=pow_pos (RG16.Literal.g_pos R.makes now) _
  have funded:‖eng‖*fare ≤ (originalRent R h i e+extra)*(regulatorRun R.family N per (i+1))^(grade target h 1):=by
    apply (div_le_iff₀ pg).mp
    have fee:=le_max_right (0:ℝ) ((‖eng‖*fare)/(regulatorRun R.family N per (i+1))^(grade target h 1)-originalRent R h i e)
    dsimp only [extra,shortfall]
    linarith only [fee]
  have heard:(Fr).coeffSize err ≤ price R h N per i target depth e extra:=by
    apply calibrated R h N per i target depth now enough q e invoice (fun W=>eng*Y W) (le_max_left ..)
    intro a ha j hj W
    rw [normed,←mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_left (nodes depth a ha j hj) (norm_nonneg _)).trans funded
  exact ⟨heard,fun a=>(single_le_sum (f:=fun k=>‖err k‖) (fun _ _=>norm_nonneg _) (mem_univ a)).trans heard⟩

end YM.Integration.WilsonOriginalFundedPageDecoder
