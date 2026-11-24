import YM.Integration.WilsonIndependentPublicRawOrbit
import YM.Integration.WilsonIndependentTwoMomentGrant

/-! The same raw orbit estimate uses an already purchased two-length
book, with its two anchored moments and every supplementary request. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentPublicRawBook
open Lattice RG XSpace XSpace.Rose XSpace.Cirrus Precision Source PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum
open RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Prim
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentRawNamedProduct WilsonIndependentMatchedNamedPair
open scoped Classical ENNReal NNReal


open WilsonIndependentPublicRawOrbit (Priced)

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
  (K:KernelChoices)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)(V:XSpace.Run)
  {H:Hol G}(P:Master H)(chart:ChartRatio G)(e h k j p b u:ℕ)(γ:ℝ)(hi:γ<1)
  (extra:ℕ)(col:G.ColorIndex)(late:4≤j)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

include hi in
theorem notebook (aperture:Requests B.a→ℝ)(positive:∀w,0≤aperture w)
    (F:Tent (M V B.a))(clock:∀ w:Requests B.a,sheet F (Page.opening _ w)=Clocks.flat)
    (paid:let C:=S V B.a B.positive j late
          let L:=WilsonIndependentGroupedOrbitBills.meter C aperture positive
          let cash:=C.leadA Y G (quantum b u)
          let T:=C.lane Y G branches (sheet F)
          Cylinder T (C.payroll Y G branches (sheet F)) (C.pushP Y G) (C.takeP Y G) L cash p b u ∧
            Lantern (C.dialect Y G branches (sheet F)) (RegulatorIR.FVAAlt2.Rocket.native _) L cash γ ∧
            T.Endings L):
    Priced R W K Y branches V B.a j B.positive late p γ aperture F := by
  let C:=S V B.a B.positive j late
  obtain ⟨cylinder,lamp,ends⟩:=paid
  intro l r d e' t t' sample o z x c₀ board reach clear safe q hq
  let L:=WilsonIndependentGroupedOrbitBills.meter C aperture positive
  have opening (w:Requests B.a): C.l (Page.opening _ w)=1:=
    (WilsonIndependentExactPlate.units V B.a B.positive j late w).1
  have same (w:Requests B.a):TopF (n V B.a) w=(sample w).F.p.side:=by
    rw [board w]
    exact WilsonIndependentExactPlate.starting V B.a w
  have fare (w:Requests B.a):ENNReal.ofReal (1+WilsonIndependentRawPairOpening.span x o z w)≤L.val w:=by
    apply le_trans _ le_self_add
    exact ENNReal.ofReal_le_ofReal (by linarith [reach w])
  obtain ⟨H,n₀,nonneg,payment⟩:=WilsonIndependentRawNamedOrbit.terminal cylinder lamp ends
    R W sample l r d e' t t' o z x opening clock same fare clear safe q hq hi
    (V.finalSide.side.val*V.ratio^B.a) (WilsonIndependentLicensedCircuit.ends V B.a B.positive)
  refine ⟨n₀,H,nonneg,fun w=>?_⟩
  have side:1≤((V.step w.val).p.side.val:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
  have fare':(L.val w).toReal=1+aperture w+Real.log ((V.step w.val).p.side.val:ℝ):=by
    change (ENNReal.ofReal (1+aperture w)+ENNReal.ofReal (Real.log ((V.step w.val).p.side.val:ℝ))).toReal=_
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith [positive w]),ENNReal.toReal_ofReal (Real.log_nonneg side)]
  have result:=payment w
  change _ ≤ H*(L.val w).toReal^n₀*((V.step w.val).p.side.val:ℝ)^(-(γ/2)) at result
  rw [fare'] at result
  exact result

include hi in
theorem original
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B):
    ∀ (aperture:Requests B.a→ℝ)(_pos:∀ w,0≤aperture w),
        let C:=S V B.a B.positive j late
        ∃ F:Tent (M V B.a), Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
          (∀ w:Requests B.a,sheet F (Page.opening _ w)=Clocks.flat) ∧
          Priced R W K Y branches V B.a j B.positive late p γ aperture F := by
  intro aperture positive C
  obtain ⟨_,F,book,clock,sale⟩:=paid aperture positive
  exact ⟨F,book,clock,notebook R W K Y branches V P chart e h k j p b u γ hi extra late B
    aperture positive F clock sale⟩

end YM.Integration.WilsonIndependentPublicRawBook
