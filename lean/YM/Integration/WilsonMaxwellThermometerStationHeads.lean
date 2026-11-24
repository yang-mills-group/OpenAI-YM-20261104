import YM.Integration.WilsonMaxwellThermometerMaximalHead
import YM.Integration.WilsonPositionThermometerGradedSource
import YM.IterationFour.Running

/-! The three signed highest-rank rows of the original positioned thermometer, at the
same station, true temperature and cutoff on each of its ordinary faces. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerStationHeads
open Function Filter RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "C"=>R.family
local notation "road"=>R.family.path.levels

def fee (k:ℕ):ℝ:=Perch.bill (-1/2) (clim road k)

theorem rate (simple:G.Simple):Tendsto (fee R) atTop (nhds 0):=by
  have mon:=Station.mag_rate road simple (b:=1) (by norm_num)
  have raised:Tendsto (road).clock.monitor atTop atTop:=by
    change Tendsto (fun k=>(road).clock.monitor k^(1:ℝ)) atTop atTop at mon
    simpa only [Real.rpow_one] using mon
  have eqn:(fee R)=fun k=>((road).clock.monitor k)^(-(1/2):ℝ):=by
    funext k
    change Real.exp (_*(-1/2)) = Real.exp _ ^ _
    rw [←Real.exp_mul]
    simp [Perch.boil, Perch.y, clim, neg_div]
  rw [eqn]
  exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/2:ℝ))).comp raised

theorem clock (simple:G.Simple):∀ᶠ k:ℕ in atTop,
    fee R k < 1 ∧ 2 ≤ (road).clock.monitor k ∧ ∀ N per,k≤N→
    0<shrink C k N per ∧ shrink C k N per≤2/(road).clock.monitor k:=by
  have mon:=Station.mag_rate road simple (b:=1) (by norm_num)
  have raised:Tendsto (road).clock.monitor atTop atTop:=by
    change Tendsto (fun k=>(road).clock.monitor k^(1:ℝ)) atTop atTop at mon
    simpa only [Real.rpow_one] using mon
  filter_upwards [(rate R simple).eventually_lt_const (by norm_num: (0:ℝ)<1),
    raised.eventually_ge_atTop 2] with k little big
  refine ⟨little,big,?_⟩
  intro N per top
  refine ⟨shrink_pos C R.makes top per,?_⟩
  let g:=(Real.sqrt ((C).path.β N per k))⁻¹
  let h:=(road).clock.hatCoupling k
  let v:=(road).clock.monitor k
  have cap:g≤2*h:=(IterationFour.Currency.hat_g R.makes N per k top).2
  have hp:0<h:=inv_pos.mpr (Real.sqrt_pos.mpr (WardBin.hot road k))
  have vp:0<v:=lt_of_lt_of_le (by norm_num : (0:ℝ)<2) big
  change g/(h*v)≤2/v
  rw [←div_div,div_le_div_iff_of_pos_right vp,div_le_iff₀ hp]
  exact cap

variable {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}

theorem original (simple:G.Simple):∀ᶠ k:ℕ in atTop, ∀ (A:Group C 6),
    A.station.k=k → A.station.checked f H A.horizon → ∀ N per, k<N →
    ∀ s (i:Fin 3),
    let j:=index A (grade i)
    let w:=A.change (grade i) (source C s i)
    let p:=ladder C j w
    let θ:=shrink C k N per
    let ρ:=Station.mag road A.station.b k
    let x:=awake C j k N per (A.station.wheel.atCut (N,per) j w)
    error ((C).labels.level j) (θ^(j.val/2)/ρ^j.val) x p ≤
      fee R k/(1-fee R k)*((C).labels.level j).coeffSize p:=by
  filter_upwards [clock R simple] with k paid
  intro A eqn checked N per hn s i
  subst k
  have enough:=paid.2.2 N per hn.le
  have θ:shrink C A.station.k N per≤1:=enough.2.trans ((div_le_one
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) paid.2.1)).mpr paid.2.1)
  have scale:1≤Station.mag road A.station.b A.station.k:=
    Real.one_le_rpow ((by norm_num:(1:ℝ)≤2).trans paid.2.1)
      (le_of_lt ((by norm_num:(0:ℝ)<5).trans checked.high.1))
  exact stationed R.makes A.station checked (index A (grade i)) _ N per hn scale θ paid.1

end YM.Integration.WilsonMaxwellThermometerStationHeads
