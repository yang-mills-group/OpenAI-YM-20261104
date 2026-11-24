import YM.Integration.WilsonSeparatedPrefixKineticEdge
import YM.Integration.WilsonSeparatedPrefixKineticForecast
import YM.Integration.WilsonSeparatedPrefixKineticWage
import YM.Integration.WilsonReportingAbsoluteInletCoordinates

/-! Every summand uses the original filed finite-volume unmarked measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticLedger
open Function Finset Filter Lattice Wilson RG RG.Supply Precision PowerSeries
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open WilsonSeparatedPrefixKineticWage WilsonOlderFreshSoftSocketKinetic WilsonReportingAbsoluteInletForecastBooks
open WilsonSeparatedPrefixKineticEdge WilsonSeparatedPrefixKineticForecast WilsonSeparatedPrefixKineticTruncation
open Pert.Asymptotics AllOrder AllOrder.Transit PhysicalNext.Repeat.Legato ConnectedActivityE6
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels
local notation "g" => regulatorRun R.family

private theorem positive {N i:ℕ}(per:ℕ)(live:i ≤ N):0<g N per i:=by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))

private theorem normalized {N i:ℕ}(per:ℕ)(live:i ≤ N):
    (R.T.history N per i).beta*(g N per i)^2=1:=by
  exact (WilsonReportingAbsoluteInletCoordinates.squared (Overlay.beta_positive R.makes.wilson (p:=per) live) zero_lt_one).2

theorem measured {N i k q:ℕ}(per:ℕ)(live:i<N)
    (physical:|(R.T.history N per i).beta-thermal R k N per i| ≤ (g N per i)^q):
    |1-(g N per i/g N per (i+1))^2*value (Burn.horizon k+2) (pitch V R.metals.O N i) (g N per (i+1))| ≤ (g N per i)^(q+2):=by
  let y:=g N per i
  let x:=g N per (i+1)
  let t:=value (Burn.horizon k+2) (pitch V R.metals.O N i) x
  let a:=(R.T.history N per i).beta
  let b:=(R.T.history N per (i+1)).beta
  have one:a*y^2=1:=normalized R per live.le
  have two:b*x^2=1:=normalized R per live
  have xx:0<x:=positive R per live
  have inv:(x^2)⁻¹=b:=(eq_inv_of_mul_eq_one_left two).symm
  have eq:(y/x)^2*t=y^2*(b*t):=by rw [div_pow,div_eq_mul_inv,inv];ring
  change |1-(y/x)^2*t| ≤ y^(q+2)
  rw [eq,←one,mul_comm a,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left physical (sq_nonneg y)).trans_eq (by rw [pow_add];ring)

private theorem addEdges {b K:ℕ}(bK:b ≤ K)(y:ℕ→ℝ)(cost:ℝ)(paid:∀i,b ≤ i→i<K→|y (i+1)-y i| ≤ cost):
    |y K-y b| ≤ (K-b:ℕ)*cost:=by
  induction K,bK using Nat.le_induction with
  | base=>simp
  | succ i hi ih=>
    have past:=ih (fun j bj ji=>paid j bj (ji.trans (Nat.lt_succ_self i)))
    have step:=paid i hi (Nat.lt_succ_self i)
    refine (abs_sub_le _ (y i) _).trans ((add_le_add step past).trans_eq ?_)
    rw [Nat.succ_sub hi,Nat.cast_succ];ring

private theorem monotone (n:ℕ){M δ w x z:ℝ}(M1:1 ≤ M)(δ0:0 ≤ δ)(x0:0 ≤ x)(dw:δ ≤ w)(xz:x ≤ z):fare n M δ x ≤ fare n M w z:=by
  unfold fare optical
  have M0:0 ≤ M:=by linarith
  have z0:0 ≤ z:=x0.trans xz
  have w0:0 ≤ w:=δ0.trans dw
  gcongr

theorem trail (simple:G.Simple){N K b n k q per:ℕ}(bK:b ≤ K)(KN:K ≤ N)(ne:n ≤ Burn.horizon k+2)
    {M t:ℝ}(M1:1 ≤ M)(t1:t ≤ 1)(small:t*M ≤ 1/2)(major:∀i,b ≤ i→i ≤ K→ g N per i ≤ t)
    (slope:∀i,b ≤ i→i<K→ g N per i/g N per (i+1) ≤ 2)
    (kin:∀i,b ≤ i→i ≤ K→mass n (kinetic V R.metals.O N K i) ≤ M)
    (wages:∀i,b ≤ i→i<K→ mass n (pace (pitch V R.metals.O N i)) ≤ M ∧ mass n (pitch V R.metals.O N i) ≤ M ∧ mass (Burn.horizon k+2) (pitch V R.metals.O N i) ≤ M)
    (physical:∀i,b ≤ i→i<K→|(R.T.history N per i).beta-thermal R k N per i| ≤ (g N per i)^q):
    |g N per K-g N per b*value n (kinetic V R.metals.O N K b) (g N per b)| ≤ (K-b:ℕ)*fare n M (t^(q+2)) t:=by
  let y(i:ℕ):=g N per i*value n (kinetic V R.metals.O N K i) (g N per i)
  have heard:=addEdges bK y (fare n M (t^(q+2)) t) (by
    intro i bi iK
    let x:=g N per (i+1)
    let r:=g N per i/x
    have x0:0<x:=positive R per (iK.trans_le KN)
    have y0:0<g N per i:=positive R per ((iK.trans_le KN).le)
    have start:constantCoeff (pitch V R.metals.O N i)=1:=angle_tilt simple (show LocalRatio R.metals.O from (RunFormalChain.fromRun R).receipt) (iK.trans_le KN)
    obtain ⟨sf,hm,he⟩:=wages i bi iK
    have xt:x ≤ t:=major _ (by omega) iK
    have M0:0 ≤ M:=zero_le_one.trans M1
    have heard:=chronological ne _ _ (kinetic V R.metals.O N K i) (pace_tax start) start (pace_cc start) x0.le (xt.trans t1) (div_nonneg y0.le x0.le) (slope i bi iK) M1 hm sf he (kin i bi iK.le) ((mul_le_mul_of_nonneg_right xt M0).trans small) (measured R per (iK.trans_le KN) (physical i bi iK))
    have exactRos:x*r=g N per i:=by dsimp [r];field_simp
    rw [backwards _ _ simple (show LocalRatio R.metals.O from (RunFormalChain.fromRun R).receipt) iK KN,exactRos] at heard
    exact heard.trans (monotone n M1 (pow_nonneg y0.le _) x0.le (pow_le_pow_left₀ y0.le (major i bi iK.le) _) xt))
  have edge:kinetic V R.metals.O N K K=1:=by rw [kinetic,dif_neg (lt_irrefl _)]
  simpa only [y,edge,one_value,mul_one] using heard

end YM.Integration.WilsonSeparatedPrefixKineticLedger
end
