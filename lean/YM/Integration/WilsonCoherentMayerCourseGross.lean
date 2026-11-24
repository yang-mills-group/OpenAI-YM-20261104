import YM.Integration.WilsonCoherentMayerPublishedGross
import YM.QuadraticLocal.Campaign.Elixir

/-! Rejected atoms at the same support margin and original cashier as the issued course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCourseGross
open Function Finset Lattice Wilson RG Marker Ac Push QuadraticLocal QuadraticLocal.Earn
open Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry
open scoped Classical BigOperators
variable {G:Gauge} {n c:Side} {V α ι:Type} [DecidableEq V]
  {P:Passport n V} {R:Census V} (X:ι→Row P R G α) (w:V→ℝ) (t:V→ℕ)
  (q:Ratio c n)(E:Earnings) (S:Press X E.cause)(book:Press.Receipt X S E.width E.merchant)
  {j k l:ℕ} {Ω W g a:ℝ} {B B':BudgetPoint}
local notation "Y"=> (Width.treasured X q S book B' E.afterwards g)
local notation "H" => ((Spill.allOver B')^E.cap)

theorem original (cash:E.Cashier G q.count B B' Ω W g)
    (roster:Scene.Armada X w t E.before Ω⁻¹ j k l)
    (jet:j≤E.cause)(count:k≤E.count)(rank:l≤E.rank)
    (exponent:a≤B'.supportExponent+1+1):
    WilsonRootedKioskOccupiedSlip.Gross Y w B'.B a (H*Ω):=by
  have seated:Scene.Armada X w t E.before Ω⁻¹ E.cause E.count E.rank:=
    ⟨⟨fun s=>(roster.quota s).trans count,fun s=>(roster.crew s).trans rank⟩,
      roster.positive,roster.suggests,⟨roster.purchases.spend,fun i=>
       ⟨((roster.purchases.usable i).1).trans jet,(roster.purchases.usable i).2⟩⟩,roster.honor⟩
  have op:0<Ω:=cash.paysAbove
  have coupler:Ω⁻¹≤1 := (inv_le_one₀ op).mpr cash.cool
  have original:WilsonRootedKioskOccupiedSlip.Gross Y w B'.B
      (B'.supportExponent+1+1) (H*E.grow G q.count B' Ω⁻¹):=
    WilsonCoherentMayerPublishedGross.original X w t B' q S book E.afterwards
      seated cash.price coupler cash.schedule cash.soon
  have normed:E.produce q.count*Ω⁻¹≤1:=by
    rw [←div_eq_mul_inv,div_le_one op]
    exact cash.earns
  have ceiling:E.grow G q.count B' Ω⁻¹≤Ω:=by
    exact (mul_le_mul_of_nonneg_left normed cash.minted.le).trans ((mul_one _).le.trans cash.quote)
  have toll (s:R.Mode):0≤Poly.toll w s:=Finset.prod_nonneg fun v _=>(roster.positive v).le
  obtain ⟨f,pay,observed,roots⟩:=original.before
  refine ⟨f,pay,observed,fun x=>budget_loosen (budget_mono (roots x) ?_ ?_) ?_⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (toll _) (pay i)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    split
    next live=>
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (toll _) (pay i))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right exponent (Nat.cast_nonneg _))
    next _=>exact le_rfl
  · exact mul_le_mul_of_nonneg_left ceiling (pow_nonneg (zero_le_one.trans (Spill.allOver_ge B')) _)

end YM.Integration.WilsonCoherentMayerCourseGross
