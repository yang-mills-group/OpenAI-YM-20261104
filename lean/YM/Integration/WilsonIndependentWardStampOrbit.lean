import YM.Integration.WilsonIndependentWardStampPair
import YM.Integration.WilsonIndependentRawNamedOrbit

/-! The genuine single-stamp/peer terminal as a real scalar on the elected reel. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentWardStampOrbit
open Lattice RG Source Labels PertExtension
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Profiles
open WilsonIndependentWardStampPair
open scoped Classical ENNReal NNReal

variable {G:Gauge}{I:Type}{M:I→ℕ}{n:Page M→Side}{S:Heir n G}{V:Reel S}{T:S.Accounts}
  {Γ:Flap M→Layer (Foot G) (Foot G)}{B:Flap M→Bride G}{L:Meter I}{cash:Flap M→ℝ≥0∞}
  {p f u m k':ℕ}{D:Choice M}{γ c₀:ℝ}{U U':Portrait G}
  (A:Cylinder V T Γ B L cash p f u)(lamp:Lantern S D L cash γ)(endings:V.Endings L)
  (K:LocalStamp U m)(K':LocalStamp U' k')(o z:I→ Cover)(x:I→Room)
  (start:∀ w,S.l (Page.opening M w)=1)
  (fare:∀ w,ENNReal.ofReal (1+WilsonIndependentRawPairOpening.span x o z w)≤L.val w)
  (clear:0<c₀)(safe:S.cushion c₀ x)

include A lamp endings start fare clear safe

theorem stopped (q:ℕ)(hq:q≤p)(J:Choice M)(older:D.age≤J.age) :
    ∃ C:ℝ,∃ k:ℕ,0≤C ∧ ∀ w,
      ‖plotPT (V.clock (Page.opening M w)) (vital (TopF n w) (convey (o w) U * convey (z w) U'))
        (m+k') q - note ((report K K' T o z).main (J.choose w) q 0)‖ ≤
        C*(L.val w).toReal^k*S.modifyErr 0 f γ J w := by
  have seed:=WilsonIndependentWardStampPair.opening K K' V T L x o z p (u+f+f) start fare
  exact WilsonIndependentRawWordOrbit.numerical A (report K K' T o z) _
    (fun w=>(issued K K' (o w) (z w)).1) lamp seed clear safe endings hq older

theorem terminal (q:ℕ)(hq:q≤p)(hi:γ<1)(Z:ℕ)(sides:∀ w,(n (Page.finallyW M w)).val≤Z) :
    ∃ C:ℝ,∃ k:ℕ,0≤C ∧ ∀ w,
      ‖plotPT (V.clock (Page.opening M w)) (vital (TopF n w) (convey (o w) U * convey (z w) U'))
        (m+k') q - note ((report K K' T o z).main (Page.finallyW M w) q 0)‖ ≤
        C*(L.val w).toReal^k*(S.P w)^(-(γ/2)) := by
  obtain ⟨C,k,hC,H⟩:=stopped A lamp endings K K' o z x start fare clear safe q hq
    (WilsonIndependentRawPeriodPower.terminal M) D.young
  let ck:=2+(Z:ℝ)^γ
  have hk:0≤ck:=by unfold ck; positivity
  refine ⟨C*ck,k,mul_nonneg hC hk,fun w=>?_⟩
  apply (H w).trans
  have cost:=WilsonIndependentRawPeriodPower.cost V γ lamp.gleams hi f Z A.positive start sides w
  exact (mul_le_mul_of_nonneg_left cost (mul_nonneg hC (by positivity))).trans_eq (by unfold ck; ring)

end YM.Integration.WilsonIndependentWardStampOrbit
