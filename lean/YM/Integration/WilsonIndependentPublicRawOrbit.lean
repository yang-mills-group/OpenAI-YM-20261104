import YM.Integration.WilsonIndependentRawNamedOrbit
import YM.Integration.WilsonIndependentPublicPlateGrant

/-! A single independent flat notebook prices both submitted and surveyed
pivot pairs. The relative aperture is elected before the notebook. Each
named physical insertion and all its lower Taylor terms use that notebook. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentPublicRawOrbit
open Lattice RG XSpace XSpace.Rose XSpace.Cirrus Precision Source PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum
open RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Prim
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentRawNamedProduct WilsonIndependentMatchedNamedPair
open scoped Classical ENNReal NNReal

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
  (K:KernelChoices)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
  (V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4≤j)

def Priced (p:ℕ)(γ:ℝ)(aperture:Requests a→ℝ)(F:Tent (M V a)) : Prop :=
  let C:=S V a ha j hj
  ∀ (l r:Bool)(d e:ℕ)(b:(R.family.labels.level d).Index)(b':(R.family.labels.level e).Index)
    (sample:Requests a → Sample 2)(o z:Requests a → Cover)(x:Requests a → Room)
    (c₀:ℝ), (∀ w,(sample w).F=V.step w.val) →
    (∀ w,WilsonIndependentRawPairOpening.span x o z w≤aperture w) → 0<c₀ →
    (C.dialect Y G branches (sheet F)).cushion c₀ x →
    ∀ q:ℕ,q≤p → ∃ k:ℕ,∃ H:ℝ,0≤H ∧ ∀ w:Requests a,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (printed R W (sample w) l d (o w) b * printed R W (sample w) r e (z w) b')) -
        (note ((report R W l r d e b b' (C.payroll Y G branches (sheet F)) o z).main
          (Page.finallyW (M V a) w) q 0):ℂ)‖ ≤
        H*(1+aperture w+Real.log ((V.step w.val).p.side.val:ℝ))^k*
          ((V.step w.val).p.side.val:ℝ)^(-(γ/2))

variable {H:Hol G}(P:Master H)(chart:ChartRatio G)(e h k j:ℕ)(p b u:ℕ)(γ:ℝ)
  (lo:0<γ)(hi:γ<1)

theorem original (simple:G.Simple)(valid:LocalRatio chart)(late:5≤j)(head:h+3≤j)
    (width:p≤u)(rate:0<b)(col:G.ColorIndex) :
    ∃ B:WilsonIndependentEvenPassport.Menu P chart K V e h k j
        (WilsonIndependentPublicPlateGrant.floor (G:=G) K j Y p b u γ lo hi),
      ∀ (aperture:Requests B.a→ℝ)(_positive:∀ w,0≤aperture w),
        let C:=S V B.a B.positive j (by omega)
        ∃ F:Tent (M V B.a), Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
          (∀ w:Requests B.a,sheet F (Page.opening _ w)=Clocks.flat) ∧
          Priced R W K Y branches V B.a j B.positive (by omega) p γ aperture F := by
  obtain ⟨B,paid⟩:=WilsonIndependentPublicPlateGrant.selected P chart K V e h k j Y branches
    p b u γ lo hi simple valid late head width rate col
  refine ⟨B,?_⟩
  intro aperture positive C
  obtain ⟨_,F,notebook,clock,cylinder,lamp,ends⟩:=paid aperture positive
  refine ⟨F,notebook,clock,?_⟩
  intro l r d e' t t' sample o z x c₀ board reach clear safe q hq
  let L:=WilsonIndependentGroupedOrbitBills.meter C aperture positive
  have opening (w:Requests B.a): C.l (Page.opening _ w)=1:=
    (WilsonIndependentExactPlate.units V B.a B.positive j (by omega) w).1
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

end YM.Integration.WilsonIndependentPublicRawOrbit
