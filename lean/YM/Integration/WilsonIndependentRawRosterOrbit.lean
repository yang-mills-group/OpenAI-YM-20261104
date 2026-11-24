import YM.Integration.WilsonIndependentRawRosterBudget
import YM.Integration.WilsonIndependentRawNamedOrbit

/-! Submit the complete ordinary product of a fixed roster on a common
Wilson inversion board and follow its normalized report to its true stop. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentRawRosterOrbit
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open WilsonIndependentRawRosterWord WilsonIndependentRawWordGeometry
open scoped Classical ENNReal NNReal

variable {G:Gauge}{I J:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    {M:J → ℕ}{n:Page M → Side}{S:Heir n G}(T:S.Accounts)
    (sites:J → I → Cover)

def report:T.Report (arms.accounts (degree R d key)):=
  declaring T (fun w=>bank R W σ d key arms (sites w))
    (fun w=>(enrolled R W σ d key arms (sites w)).2)

theorem opening (V:Reel S)(L:Meter J)(x:J → Room)(p u:ℕ)
    (start:∀w,S.l (Page.opening M w)=1)
    (fare:∀w,ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms) ≤ L.val w):
    WilsonIndependentRawWordTransport.Opening (p:=p) (x:=x) (u:=u) (L:=L)
      (report R W σ d key arms T sites) (wage:=1):=by
  intro j _ r
  apply Carry.regular
  refine ⟨_,arms.accounts (fun _=>u+u),WilsonIndependentRawRosterBudget.finite R W σ d key arms (u+u) j r,?_⟩
  intro w
  change markQ (S.coverQ x u (Page.opening M w)) (bank R W σ d key arms (sites w) j r) ≤ _
  rw [WilsonIndependentRawPairOpening.seated V x start w u r]
  apply (WilsonIndependentRawRosterBudget.original R W σ d key arms (x w) (sites w) u j r).trans
  exact mul_le_mul_right (pow_le_pow_left' (fare w) _) _

variable {T}{V:Reel S}{Γ:Flap M → Layer (Foot G) (Foot G)}{B:Flap M → Bride G}
    {L:Meter J}{cash:Flap M → ℝ≥0∞}{p f u:ℕ}{D:Choice M}{γ c₀:ℝ}
    (A:Cylinder V T Γ B L cash p f u)(lamp:Lantern S D L cash γ)(endings:V.Endings L)
    (sample:J → Sample 2)(x:J → Room)
    (start:∀w,S.l (Page.opening M w)=1)(clock:∀w,V.clock (Page.opening M w)=Clocks.flat)
    (same:∀w,TopF n w=(sample w).F.p.side)
    (fare:∀w,ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms) ≤ L.val w)
    (clear:0<c₀)(safe:S.cushion c₀ x)
include A lamp endings start clock same fare clear safe

theorem stopped (q:ℕ)(hq:q ≤ p)(stop:Choice M)(older:D.age ≤ stop.age):
    ∃ C:ℝ,∃ k:ℕ,0 ≤ C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (film R W σ d key (sample w) (sites w) arms))-
        (note ((report R W σ d key arms T sites).main (stop.choose w) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*S.modifyErr 0 f γ stop w:=by
  let Z:=report R W σ d key arms T sites
  let U:=fun w=>body R W σ d key arms (sites w)
  have seed:=opening R W σ d key arms T sites V L x p (u+f+f) start fare
  obtain ⟨C,k,hC,money⟩:=WilsonIndependentRawWordOrbit.numerical A Z U
    (fun w=>(enrolled R W σ d key arms (sites w)).1) lamp seed clear safe endings hq older
  refine ⟨C,k,hC,fun w=>?_⟩
  have hw:=money w
  rw [clock w,same w] at hw
  rw [hearing,←Complex.ofReal_sub,Complex.norm_real]
  exact hw

theorem terminal (q:ℕ)(hq:q ≤ p)(hi:γ<1)(last:ℕ)(sides:∀w,(n (Page.finallyW M w)).val ≤ last):
    ∃ C:ℝ,∃ k:ℕ,0 ≤ C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (film R W σ d key (sample w) (sites w) arms))-
        (note ((report R W σ d key arms T sites).main (Page.finallyW M w) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*(S.P w)^(-(γ/2)):=by
  obtain ⟨C,k,hC,price⟩:=stopped R W σ d key arms sites A lamp endings sample x start clock same fare
    clear safe q hq (WilsonIndependentRawPeriodPower.terminal M) D.young
  let ck:=2+(last:ℝ)^γ
  have hk:0 ≤ ck:=by unfold ck; positivity
  refine ⟨C*ck,k,mul_nonneg hC hk,fun w=>?_⟩
  apply (price w).trans
  have bill:=WilsonIndependentRawPeriodPower.cost V γ lamp.gleams hi
    f last A.positive start sides w
  exact (mul_le_mul_of_nonneg_left bill (mul_nonneg hC (by positivity))).trans_eq (by unfold ck;ring)

end YM.Integration.WilsonIndependentRawRosterOrbit
