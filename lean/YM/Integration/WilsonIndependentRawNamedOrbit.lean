import YM.Integration.WilsonIndependentRawPairOpening
import YM.Integration.WilsonIndependentRawPeriodPower

/-! The genuine raw normalized orbit reading and its own cover report,
with a single finite, translated pair of stencils and the actual old
quiet history. The choice of either section is made before the test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawNamedOrbit
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open WilsonIndependentRawNamedProduct WilsonIndependentRawPairOpening
open WilsonIndependentMatchedNamedPair
open scoped Classical ENNReal NNReal

variable {G:Gauge}{I:Type}{M:I→ℕ}{n:Page M→Side}{S:Heir n G}{V:Reel S}{T:S.Accounts}
  {Γ:Flap M→Layer (Foot G) (Foot G)}{B:Flap M→Bride G}{L:Meter I}{cash:Flap M→ℝ≥0∞}
  {p f u:ℕ}{D:Choice M}{γ c₀:ℝ}
  (A:Cylinder V T Γ B L cash p f u) (lamp:Lantern S D L cash γ)(endings:V.Endings L)
  (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(sample:I → Sample 2)
  (a c:Bool)(d e:ℕ)(b:(R.family.labels.level d).Index)(b':(R.family.labels.level e).Index)
  (o z:I → Cover)(x:I → Room)
  (start:∀ w,S.l (Page.opening M w)=1)(clock:∀ w,V.clock (Page.opening M w)=Clocks.flat)
  (same:∀ w,TopF n w=(sample w).F.p.side)
  (fare:∀ w,ENNReal.ofReal (1+span x o z w)≤L.val w)
  (clear:0<c₀)(safe:S.cushion c₀ x)

include A lamp endings start clock same fare clear safe

theorem stopped (q:ℕ)(hq:q≤p)(J:Choice M)(older:D.age≤J.age) :
    ∃ C:ℝ,∃ k:ℕ,0≤C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (printed R W (sample w) a d (o w) b * printed R W (sample w) c e (z w) b')) -
        (note ((report R W a c d e b b' T o z).main (J.choose w) q 0):ℂ)‖ ≤
        C*(L.val w).toReal^k*S.modifyErr 0 f γ J w := by
  let Z:=report R W a c d e b b' T o z
  let U:=fun w=>word R W a c d e b b' (o w) (z w)
  have seed:=WilsonIndependentRawPairOpening.original V x o z R W a c d e b b'
    T L p (u+f+f) start fare
  obtain ⟨C,k,hC,H⟩:=WilsonIndependentRawWordOrbit.numerical A Z U
    (opening R W a c d e b b' T o z) lamp seed clear safe endings hq older
  refine ⟨C,k,hC,fun w=>?_⟩
  have hc:=H w
  rw [clock w,same w] at hc
  rw [hearing,←Complex.ofReal_sub,Complex.norm_real]
  exact hc

theorem terminal (q:ℕ)(hq:q≤p)(hi:γ<1)(K:ℕ)(sides:∀ w,(n (Page.finallyW M w)).val≤K) :
    ∃ C:ℝ,∃ k:ℕ,0≤C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (printed R W (sample w) a d (o w) b * printed R W (sample w) c e (z w) b')) -
        (note ((report R W a c d e b b' T o z).main (Page.finallyW M w) q 0):ℂ)‖ ≤
        C*(L.val w).toReal^k*(S.P w)^(-(γ/2)) := by
  obtain ⟨C,k,hC,H⟩:=stopped A lamp endings R W sample a c d e b b' o z x
    start clock same fare clear safe q hq (WilsonIndependentRawPeriodPower.terminal M) D.young
  let ck:=2+(K:ℝ)^γ
  have hk:0≤ck:=by unfold ck; positivity
  refine ⟨C*ck,k,mul_nonneg hC hk,fun w=>?_⟩
  apply (H w).trans
  have cost:=WilsonIndependentRawPeriodPower.cost V γ lamp.gleams hi
    f K A.positive start sides w
  exact (mul_le_mul_of_nonneg_left cost (mul_nonneg hC (by positivity))).trans_eq (by unfold ck; ring)

end YM.Integration.WilsonIndependentRawNamedOrbit
