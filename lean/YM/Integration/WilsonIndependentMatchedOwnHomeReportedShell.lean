import YM.Integration.WilsonIndependentMatchedOwnHomeAxisWage
import YM.Integration.WilsonIndependentSpoutMasterObserved

/-! A finite stopped scalar row at the lower kinetic is read by the measured
clock of the same history. The measured high-order shell costs only a
polynomial in the optical interval in addition to its own genuine row roof. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeReportedShell
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{e:ℕ}{E W V:Credit}

def reading (A:Levels G)(O:ChartRatio G)(N m v q:ℕ)(g:ℝ)(row:ℕ→ℝ):ℂ:=
    cash q g (embed (report A O N m v (PowerSeries.mk row)))

theorem original (H:Hol G)(F:SealR G)(e:ℕ)(E W V:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_fund:PassportC H R F W V)(N m v:ℕ),
    R.anchor ≤ v → v ≤ m → m ≤ N → ∀(row:ℕ→ℝ)(bill:ℝ), (∀i ≤ e,‖row i‖ ≤ bill) →
    ∀(J:ℕ)(g:ℝ),J ≤ e → |g| ≤ 1 →
    ‖reading R.draws R.paid N m v e g row-reading R.draws R.paid N m v J g row‖ ≤
      (Finset.Ico (J+1) (e+1)).card*|g|^(J+1)*((e+1)*C.buy (Compar R.draws.S R.y v m)*bill):=by
  obtain ⟨C,clock⟩:=SeasonC e H F.ans F.path E W V
  refine ⟨C,?_⟩
  intro R fund N m v gate before top row bill paid J g depth small
  let I:WindowS G (e+1) E:=⟨fund.f.arch.V,v,m-v,N,N,N,fund.tap.trans_le gate,by omega,le_rfl,le_rfl⟩
  let S:CourseS H F.ans F.path e E W V:=⟨fund.f,I,rfl⟩
  have age:S.Age=Compar R.draws.S R.y v m:=by
    change fund.f.arch.V.y v+(fund.f.arch.V.draws.S.scale (v+(m-v))-_)+_=_
    rw [Nat.add_sub_of_le before,fund.depths,fund.lands];rfl
  let Z:=Compar R.draws.S R.y v m
  have warm:1≤Z:=by change 1≤Compar R.draws.S R.y v m;rw [←age];exact I.warm
  have charge:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase warm)
  have clocked (j l:ℕ)(hj:j ≤ e)(hl:l ≤ e):
      ‖PowerSeries.coeff j ((relativeC R.draws R.paid N v (m-v))^l)‖ ≤ C.buy Z:=by
    have quote:=(clock S j l hj hl).main
    rw [age] at quote
    change ‖PowerSeries.coeff j ((relativeC fund.f.arch.V.draws fund.f.arch.V.paid N v (m-v))^l)‖ ≤ _ at quote
    simpa only [fund.lands,fund.modes] using quote
  let data:=report R.draws R.paid N m v (PowerSeries.mk row)
  have positive:0≤bill:=(norm_nonneg _).trans (paid 0 (Nat.zero_le _))
  have bound (j:ℕ)(hj:j ≤ e):‖PowerSeries.coeff j data‖ ≤ (e+1)*C.buy Z*bill:=by
    dsimp only [data,report]
    rw [reelQuote]
    calc
      _ ≤ ∑_l∈Finset.range (j+1),bill*C.buy Z:=by
        apply (norm_sum_le ..).trans
        apply Finset.sum_le_sum;intro l hl
        rw [norm_mul,PowerSeries.coeff_mk]
        exact mul_le_mul (paid l (by have:=Finset.mem_range.mp hl;omega))
          (clocked (j-l) l (by omega) (by have:=Finset.mem_range.mp hl;omega)) (norm_nonneg _) positive
      _ = ((j:ℝ)+1)*C.buy Z*bill:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring
      _ ≤ _:=by gcongr
  let A:=embed data
  have terms (j:ℕ)(hj:j∈Finset.Ico (J+1) (e+1)):
      ‖(g:ℂ)^j*PowerSeries.coeff j A‖≤|g|^(J+1)*((e+1)*C.buy Z*bill):=by
    have idx:=Finset.mem_Ico.mp hj
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul (pow_le_pow_of_le_one (abs_nonneg g) small idx.1) _ (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
    simpa only [A,embed,PowerSeries.coeff_map,Complex.coe_algebraMap,Complex.norm_real] using bound j (Nat.le_of_lt_succ idx.2)
  change ‖cash e g A-cash J g A‖≤_
  unfold WilsonPhysicalMarkedDefect.RawBank.cash
  rw [←Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ depth)]
  calc
    _≤∑_j∈Finset.Ico (J+1) (e+1),|g|^(J+1)*((e+1)*C.buy Z*bill):=(norm_sum_le ..).trans (Finset.sum_le_sum terms)
    _=_:=by simp only [Finset.sum_const,nsmul_eq_mul];ring
end YM.Integration.WilsonIndependentMatchedOwnHomeReportedShell
end
