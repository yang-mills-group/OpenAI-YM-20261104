import YM.Integration.WilsonMeasuredPublicEntranceJoinedEar
import YM.Integration.WilsonCapturedPrimaryPointMatrixClock
/-! A fixed optical order before the two original cutoffs pays the entire
signed heterogeneous public-head switch on every occupied face. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFixedBill
open Function Finset Filter Lattice Wilson RG Source Labels PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories.Motion
open WilsonReflectedPublicGuardedColumns WilsonThermometerUnitFilingFieldRange WilsonReflectedPublicCommonSoftLaw
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceCropRoof
open WilsonOriginalOccupiedStencil Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
def az (d:V → ℕ):ℕ:=(∑v,d v)+2
def depth (d:V → ℕ)(t:ℕ):ℕ:=az d*Fintype.card V+(t+1)+2
def order (t:ℕ):ℕ:=2*(t+1)

omit [DecidableEq V] in
theorem smooth (d:V → ℕ)(simple:G.Simple):
    ∀ᶠ f:ℕ in atTop,∀(t:ℕ)(vs:List V),vs.length≤Fintype.card V →
    let H:=R.family.path.levels.clock.hatBeta f
    let a:=fun i=>gross R (d i) f
    let e:=fun i=>net R (d i) f (depth d t)
    route a (fun i=>a i+e i) e vs ≤ (H^(t+1))⁻¹:=by
  let A:=fun i=>3*orbitCost (R.family.labels.level (d i))*(6+basisCost G (d i))
  let B:=fun i=>(6+basisCost G (d i))*(2+orbitCost (R.family.labels.level (d i)))
  have basis(i:V):0≤basisCost G (d i):=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) (d i)).choose_spec.1
  have orbit(i:V):0≤orbitCost (R.family.labels.level (d i)):=zero_le_one.trans (orbitCost_one_le _)
  have ap(i):0≤A i:=mul_nonneg (mul_nonneg (by norm_num) (orbit i)) (by linarith only [basis i])
  have bp(i):0≤B i:=mul_nonneg (by linarith only [basis i]) (by linarith only [orbit i])
  have rise:=RG01.Physical.hats simple R.family.path.levels
  filter_upwards [rise.eventually_ge_atTop (∑i:V,(A i+B i)),rise.eventually_ge_atTop (Fintype.card V:ℝ)] with f cash card
  intro t vs len H a e
  have one:1≤H:=(R.family.path.levels.fits.delayed f).le
  have hp:0<H:=zero_lt_one.trans_le one
  have heads(i:V):A i+B i≤H:=(Finset.single_le_sum (fun i _=>add_nonneg (ap i) (bp i)) (Finset.mem_univ i)).trans cash
  have held(i:V):0≤a i:=mul_nonneg (ap i) (pow_nonneg hp.le _)
  have eps(i:V):0≤e i:=mul_nonneg (bp i) (inv_nonneg.mpr (pow_nonneg hp.le _))
  have short(i:V):e i≤B i:=by
    change B i*(H^_)⁻¹≤B i
    exact mul_le_of_le_one_right (bp i) (inv_le_one_of_one_le₀ (one_le_pow₀ one))
  have mix(i:V):a i+e i≤H^(az d):=by
    have count:d i≤∑v,d v:=Finset.single_le_sum (fun v _=>Nat.zero_le (d v)) (Finset.mem_univ i)
    calc a i+e i≤A i*H^(d i+1)+B i*H^(d i+1):=
           add_le_add le_rfl ((short i).trans (le_mul_of_one_le_right (bp i) (one_le_pow₀ one)))
         _ =(A i+B i)*H^(d i+1):=(add_mul ..).symm
         _ ≤H*H^(d i+1):=mul_le_mul_of_nonneg_right (heads i) (pow_nonneg hp.le _)
         _ ≤H^(az d):=by rw [←pow_succ'];apply pow_le_pow_right₀ one;dsimp [az];omega
  let E:=H*(H^(depth d t))⁻¹
  have ep:0≤E:=mul_nonneg hp.le (inv_nonneg.mpr (pow_nonneg hp.le _))
  have close(i:V):e i≤E:=mul_le_mul_of_nonneg_right
    ((le_add_of_nonneg_left (ap i)).trans (heads i)) (inv_nonneg.mpr (pow_nonneg hp.le _))
  have tot: (vs.length:ℝ)≤H:=(Nat.cast_le.mpr len).trans card
  have step:=WilsonMeasuredPublicEntranceCropRate.route_cap a (fun i=>a i+e i) e
    (one_le_pow₀ one (n:=az d)) ep held (fun i=>add_nonneg (held i) (eps i)) eps
    (fun i=>(le_add_of_nonneg_right (eps i)).trans (mix i)) mix close vs
  calc _ ≤(vs.length:ℝ)*(H^az d)^vs.length*E:=step.2
       _ ≤H*(H^az d)^(Fintype.card V)*E:=mul_le_mul_of_nonneg_right
         (mul_le_mul tot (pow_le_pow_right₀ (one_le_pow₀ one) len) (by positivity) hp.le) ep
       _ =(H^(t+1))⁻¹:=by
         simp only [E,depth,←pow_mul,pow_add,pow_two];field_simp

theorem original (d:V → ℕ)(simple:G.Simple)(box t:ℕ):
    ∀ᶠ f:ℕ in atTop,∀N per:ℕ,f≤N → ∀l:ℕ,l≤box → ∀s:(Stock.census V).Mode,
      let H:=R.family.path.levels.clock.hatBeta f
      let a:=fun i=>gross R (d i) f
      let e:=fun i=>net R (d i) f (depth d t)
      let P:=order t
      let L:=l+Fintype.card V*l
      route a (fun i=>a i+e i) e s.val.toList+((shares s.val.toList).length:ℝ)*
        ((H^P)⁻¹+((H^P)⁻¹+(regulatorRun R.family N per f)^P*roof s L)+(H^P)⁻¹)≤(H^t)⁻¹:=by
  let r:=t+1
  let mass (s:(Stock.census V).Mode)(l:Fin (box+1)):ℝ:=((shares s.val.toList).length:ℝ)*
    (3+2^r* |roof s (l.val+Fintype.card V*l.val)|)
  have mp(s l):0 ≤ mass s l:=by dsimp [mass];positivity
  let total:=∑s,∑l,mass s l
  filter_upwards [smooth R d simple,(RG01.Physical.hats simple R.family.path.levels).eventually_ge_atTop (1+total)] with f priced ready
  intro N per fn l bl s H a e P L
  have one:1≤H:=(R.family.path.levels.fits.delayed f).le
  have hp:0<H:=zero_lt_one.trans_le one
  let g:=regulatorRun R.family N per f
  let D:=(H^r)⁻¹
  have dp:0≤D:=inv_nonneg.mpr (pow_nonneg hp.le _)
  have inv:(H^P)⁻¹≤D:=inv_anti₀ (pow_pos hp r) (pow_le_pow_right₀ one (by dsimp [P,order,r];omega))
  have paid:=WilsonCapturedPrimaryPointMatrixClock.band R (per:=per) fn
  have gcd:g^P≤2^r*D:=by
    apply (le_mul_inv_iff₀ (pow_pos hp r)).mpr
    change g^(2*r)*H^r≤2^r
    rw [pow_mul,←mul_pow,mul_comm (g^2)]
    exact pow_le_pow_left₀ (mul_nonneg hp.le (sq_nonneg g)) paid _
  have item:(H^P)⁻¹+((H^P)⁻¹+g^P*roof s L)+(H^P)⁻¹≤(3+2^r* |roof s L|)*D:=by
    have gpos:0≤g^P:=pow_nonneg (by dsimp [g,regulatorRun];positivity) _
    have up:=mul_le_mul (le_abs_self (roof s L)) gcd gpos (abs_nonneg _)
    linarith only [inv,show g^P*roof s L≤2^r* |roof s L| *D by nlinarith only [up]]
  let l₀:Fin (box+1):=⟨l,Nat.lt_succ_of_le bl⟩
  have used:mass s l₀≤total:=(Finset.single_le_sum (fun l _=>mp s l) (Finset.mem_univ l₀)).trans
    (Finset.single_le_sum (fun s _=>Finset.sum_nonneg (fun l _=>mp s l)) (Finset.mem_univ s))
  have head:=priced t s.val.toList (by simpa only [Finset.length_toList] using Finset.card_le_univ s.val)
  calc _ ≤D+mass s l₀*D:=add_le_add head (by
           apply (mul_le_mul_of_nonneg_left item (by positivity :0≤((shares s.val.toList).length:ℝ))).trans_eq
           dsimp [mass,L,l₀];ring)
       _ ≤H*D:=by rw [←one_add_mul];exact mul_le_mul_of_nonneg_right ((add_le_add_right used 1).trans ready) dp
       _ =(H^t)⁻¹:=by dsimp [D,r];rw [pow_succ,mul_inv_rev];field_simp

end YM.Integration.WilsonMeasuredPublicEntranceFixedBill
end
