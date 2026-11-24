import YM.Integration.WilsonMeasuredPublicEntranceGridCurrency
import YM.Integration.WilsonMeasuredPublicEntranceGridCompensation
import YM.Integration.WilsonMeasuredPublicEntranceTrialLamp

/-! Compare the actual normalized original physical head with the original
filed guarded lamp at every finite held field. The complete signed forced
part of each discrepancy is kept on its own original register. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRegisteredExchange
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker QuadraticLocal Extra.Histories Relay
open PhysicalNext PhysicalNext.Repeat Legato Work.G08 WilsonThermometerReflectedTrajectory
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonOriginalNullCorridor
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceGridDebit
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntranceCheapField
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V I T:Type}[DecidableEq V]{J:Census V}{N p f n:ℕ}
variable (d j:V→ℕ)(o:V → Site (R.family.side f p))(W:Rep G (R.family.side f p))
    (X H : (v:V) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
    (A:(v:V)→ R.family.label (d v) ≃ₗ[ℂ] R.family.label (d v))
    (names:(v:V)→ R.family.label (d v))(c:V→ℂ)
    (E:Lamps T I G W.p o J)(x:T)
local notation "P" => R.family.path.rep N p f
local notation "xy" => fun v => (A v).symm (fitted R (d v) (j v) N p (names v))
local notation "sig" => fun v=> -(c v)/(R.family.S.a f:ℂ)^(d v)
local notation "true_" v:max => (X v).density (o v) (R.family.localSection (d v)) (P)
local notation "file_" v:max => (H v).density (o v) (R.family.localSection (d v)) W
local notation "arm_" => WilsonOriginalAlternativeTrialSource.arm R d N p (f+n)
    (WilsonOriginalAlternativeTrialGrid.pins R p f n o) xy
    (fun i=>c i*WilsonOriginalAlternativeTrialGrid.factor R d f n i)

theorem original (live:f+n≤N)(same:W.eval=(P).eval)
    (debit:∀v,settled R (d v) (j v) f n N p live (A v) (names v) (o v))
    (physical:∀v U,(true_ v) U=(P).eval U • actualTransport R.family (N:=N)
        (fun S=>c v*R.family.O N p (names v) (anchorAt R (o v) N) S) (by omega) U)
    (empty:∀v,(H v).x=0 ∧ (H v).regular=0)
    (former:∀v U,(file_ v) U/(W.eval U:ℂ)=
      actualTransport R.family (N:=N) (arm_ v) (Nat.le_add_right f n) U - (E.log x U).part (J.fire v)):
    ∃ Z, WilsonMeasuredPublicEntranceGridCompensation.earned R (n:=n) (N:=N) d j o Z A names ∧
      ∀vs:List V,∀U,
        let a:=fun v=>regular R d (P) o X v U
        let b:=fun v=>(E.log x U).part (J.fire v)
        let e:=fun v=>sig v*regular R d (P) o Z v U
        let hard:=fun v=>account (X v) (P) U - account (H v) W U - sig v*account (Z v) (P) U
        ((P).eval U:ℂ)*((vs.map a).prod-(vs.map b).prod)=
          ((P).eval U:ℂ)*route a (fun v=>a v-e v) e vs-route b (fun v=>a v-e v) hard vs:=by
  classical
  have cut:f≤N:=by omega
  choose Z cash joint using debit
  refine ⟨Z,cash,?_⟩
  intro vs U a b e hard
  apply WilsonMeasuredPublicEntranceCheapOrder.original
  intro v
  have nonzero:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut U).ne'
  have af:((R.family.S.a f:ℂ)^(d v))≠0:=pow_ne_zero _ (by exact_mod_cast (R.family.S.a_pos f).ne')
  have truth:=physical v U
  rw [WilsonMeasuredPublicEntranceGridCurrency.physical,Complex.real_smul] at truth
  have file:=former v U
  rw [same,WilsonMeasuredPublicEntranceGridCurrency.trial] at file
  have zero:(H v).exponentialEntry (o v) (R.family.localSection (d v)) W U=0:=by
    simp [Coefficient.exponentialEntry,Coefficient.maskedTerm,(empty v).1,(empty v).2,masked,SectionData.places,SectionData.evaluate]
  change (W.eval U* (H v).exponentialEntry (o v) (R.family.localSection (d v)) W U+account (H v) W U) / _ = _ at file
  rw [zero,mul_zero,zero_add] at file
  have lower:= (div_eq_iff nonzero).mp file
  have real:((P).eval U:ℂ)*b v+account (H v) W U=((P).eval U:ℂ)*
      (c v*actualTransport R.family (N:=N) (trial R (d v) f n N p (o v) (xy v)) (Nat.le_add_right f n) U):=by
    dsimp only [b]
    linear_combination lower
  have bank:(true_ v) U-(((P).eval U:ℂ)*b v+account (H v) W U)=
      sig v*(Z v).density (o v) (R.family.localSection (d v)) (P) U:=by
    rw [truth, real, ← mul_sub, ← mul_sub,joint v U]
    field_simp
  change ((P).eval U:ℂ)*(b v-(regular R d (P) o X v U-sig v*regular R d (P) o Z v U))=
    account (X v) (P) U-account (H v) W U-sig v*account (Z v) (P) U
  simp only [regular,Coefficient.density,account] at bank ⊢
  linear_combination -bank

end YM.Integration.WilsonMeasuredPublicEntranceRegisteredExchange
end
