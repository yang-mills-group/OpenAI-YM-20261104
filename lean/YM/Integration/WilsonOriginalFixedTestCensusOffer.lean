import YM.Integration.WilsonOriginalDatedCensusInput

/-! The actual signed rent of the selected dated post and the inverse price of its named seats. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusOffer
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books) {V:Type}[Fintype V][DecidableEq V]
  {S:V→ℝ}{a:ℕ}{submitted:Config G (R.family.side (i+1) per)→Poly (Stock.census V)}
  (pub:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted)
local notation "H" => R.family.path.levels.clock.hatBeta i

/-- Transport the actual publisher's prechosen tolerance. The count and rent belong to its returned post. -/
theorem high_rent {c:ℕ}{rate bound:ℝ}(seats:pub.seats=c)(same:pub.post.rent=rate)
    (paid:(8*(budgetR R i)^c)*rate≤bound):
    (8*(budgetR R i)^pub.post.op.count)*pub.post.rent≤bound:=by
  simpa only [pub.post.capacity,seats,same] using paid

/-- All occupied peers keep their original faces on this wallet, including the stored marked scalar. -/
theorem inverse (s:(Stock.census V).Mode):
    (Poly.toll pub.post.w s)⁻¹ ≤ H^a*Poly.toll S s:=by
  have bound:=pub.appointment.wage pub.x s
  rw [pub.appointment.radius pub.x] at bound
  have base:1≤(WilsonOriginalOccupiedSalary.debit (pub.appointment.row pub.x).regular
    (pub.appointment.row pub.x).hard)^s.val.card:=one_le_pow₀ (le_max_left ..)
  simpa only [one_div] using (div_le_iff₀ (Poly.worth pub.post.salary.positive s)).mpr (base.trans bound)

/-- Restore the invoice only for occupied seats. Fresh grade, unit and any ordering of the peers are allowed. -/
theorem occupied (s:(Stock.census V).Mode) (charges:V→ℕ)
    (nn:∀v,0≤S v)(bought:∀v,S v≤H^(charges v)):
    (Poly.toll pub.post.w s)⁻¹ ≤ H^(a+∑v∈s.val,charges v):=by
  have H0:0≤H:=zero_le_one.trans (R.alloy.B.a.fits.delayed i).le
  refine (inverse R hk D Q π Γ Ψ books hi ahead pub s).trans ?_
  rw [pow_add,Poly.toll,←Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _=>nn v) (fun v _=>bought v)) (pow_nonneg H0 a)

/-- The actual inverse after a single fresh shrink, for each selected face rather than every old root. -/
theorem restored (s:(Stock.census V).Mode)(δ:ℝ)(nn:0≤δ):
    (Poly.toll (Stoop.radius pub.post.w δ) s)⁻¹ ≤ δ^s.val.card*(H^a*Poly.toll S s):=by
  have eq:(Poly.toll (Stoop.radius pub.post.w δ) s)⁻¹=δ^s.val.card*(Poly.toll pub.post.w s)⁻¹:=by
    simp only [Stoop.radius,Poly.toll,div_eq_inv_mul,Finset.prod_mul_distrib,Finset.prod_const,
      mul_inv,inv_pow,inv_inv]
  rw [eq]
  exact mul_le_mul_of_nonneg_left (inverse R hk D Q π Γ Ψ books hi ahead pub s) (pow_nonneg nn _)

end YM.Integration.WilsonOriginalFixedTestCensusOffer
end
