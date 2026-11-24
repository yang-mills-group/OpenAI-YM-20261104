import YM.Integration.WilsonThermometerHostedLamp
import YM.Integration.WilsonThermometerSameWalkSectionFare

/-! The canonical physical source pays one pre-regulator width for its full regular row and its derivative-paid truncation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerHostedCurrency
open Function Filter Finset Lattice Wilson RG Source Labels Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open Next.Foundations Push.Local PhysicalNext PhysicalNext.Repeat Legato
open RG05Readout Native Extra.Histories Push.AbsoluteSums
open WilsonOriginalStarPrimaryCatalog WilsonRetainedMarkedInletRegular WilsonThermometerHostedLamp
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "β" i => (C₀).path.levels.clock.hatBeta i

def charge (b B:ℝ) (u:ℕ):ℝ:=1+b^6*(1+B)+b^(3*u+2)*B

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (C₀).path.levels) :
    ∀ᶠ k:ℕ in atTop, ∀ N p (live:k≤N) (ref:(C₀).ref d≤k) (_:((C₀).path.levels.params k).supportExponent=100)
    {V T:Type} [DecidableEq V] [Fintype V] {J:Census V} (o:V → Site ((C₀).side k p)) (v:V)
    (q:Coefficient ((C₀).labels.level d) ((C₀).side k p)) (t:T→ℂ) (w:V→ℝ) (_:∀i,0<w i)
    (u:ℕ){B κ:ℝ},
    let P:=(C₀).path.rep N p k
    let a:=P.p.supportExponent
    let cut:=WilsonThermometerSameWalkWindow.length u (β k)
    ∀ fit:q.Format (o v) (C₀).params P,
    q.remBound (o v) P κ B → ((C₀).labels.level d).coeffSize q.x≤1+B →
    (∀x,‖t x‖≤1) → w v*charge (β k) B u≤1/3 →
    (enrolled (J:=J) R live ref o v q fit t (fun _=>True)).Paid w P.p.B (a-1) (1/3) ∧
    (enrolled (J:=J) R live ref o v q fit t (WilsonOriginalDepositedRegularWindow.small P q cut)).Paid w P.p.B (a+2) (1/3):=by
  filter_upwards [WilsonThermometerSameWalkSectionFare.original R d simple pace book,WilsonThermometerSameWalkWindow.original R simple book,
    (RG01.Physical.hats simple (C₀).path.levels).eventually_ge_atTop 2] with k primary reg high N p live ref fixed V T de fe J o v q t w pos u B κ P a cut fit bill size ht refund
  let F:=(C₀).labels.level d
  have budget:P.p=(C₀).path.levels.budget k:=(R.makes.wilson.represents N p k live).vac
  have base:a=100:=by dsimp only [a];rw [budget];exact fixed
  have crop:=WilsonThermometerHostedLamp.cropped (J:=J) R live ref o v q fit t w pos ht bill cut
  have full:=WilsonThermometerHostedLamp.complete (J:=J) R live ref o v q fit t w pos ht bill
  have head:rent R N p k d o v q.x w (a+2)≤(β k)^6*(w v*F.coeffSize q.x):=by
    simpa only [base,show (100:ℝ)+2=100+1+1 by norm_num] using primary N p live fixed o v q.x w (pos v).le
  have lower:rent R N p k d o v q.x w (a-1)≤rent R N p k d o v q.x w (a+2):=by
    apply Finset.sum_le_sum
    intro i _
    have raw:=ActualRunPhysicalPages.priced R N p k d live ref (F.core q.x) (o v)
    have amount0:0≤amount R N p k d o v q.x i:=by
      unfold amount
      split
      · exact norm_nonneg _
      · exact mul_nonneg (by unfold moving;positivity) raw.2.1
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pos v).le amount0)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  have edge:Real.exp (3*(cut:ℝ))*WilsonRetainedMarkedInletRegular.cost P.p≤(β k)^(3*u+2):=(reg p P budget u).1
  have nonneg:0≤B:=rem_nonneg bill
  have cost0:0≤WilsonRetainedMarkedInletRegular.cost P.p:=by unfold WilsonRetainedMarkedInletRegular.cost;positivity
  have soft:WilsonRetainedMarkedInletRegular.cost P.p≤Real.exp (3*(cut:ℝ))*WilsonRetainedMarkedInletRegular.cost P.p:=
    le_mul_of_one_le_left cost0 (Real.one_le_exp (by positivity))
  have wages:0≤w v*B:=mul_nonneg (pos _).le nonneg
  have allMoney:(β k)^6*(w v*F.coeffSize q.x)+(β k)^(3*u+2)*(w v*B)≤1/3:=by
    calc
      _ ≤ (β k)^6*(w v*(1+B))+(β k)^(3*u+2)*(w v*B):=by
        gcongr;exact (pos v).le
      _ ≤ w v*charge (β k) B u:=by unfold charge;nlinarith only [(pos v).le]
      _ ≤ _:=refund
  constructor
  · apply Lamps.loan_monotone _ full
    exact (add_le_add (lower.trans head) (mul_le_mul_of_nonneg_right (soft.trans edge) wages)).trans allMoney
  · apply Lamps.loan_monotone _ crop
    exact (add_le_add head (mul_le_mul_of_nonneg_right edge wages)).trans allMoney

end YM.Integration.WilsonThermometerHostedCurrency
