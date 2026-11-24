import YM.Integration.WilsonThermometerUnitFilingSchedule

/-! A common stop on the original forecast calendar. Its selection precedes both
the upper lattice and its period. The actual temperature and original stage
columns pay the signed scalar transport at that same stop. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingSpan
open Filter Finset Lattice RG Wilson Overlay PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG16 ConnectedActivityE6
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "hat!" i:max => R.family.path.levels.clock.hatBeta i

private theorem small {D:ℝ} (dp:0≤D):∀ᶠ x:ℝ in atTop,D*(1+Real.log x)≤x/2:=by
  have high : 0 < 4*(D+1):=by linarith
  have little:=Real.isLittleO_log_id_atTop.bound (show 0<(1:ℝ)/(4*(D+1)) from one_div_pos.mpr high)
  filter_upwards [little,eventually_ge_atTop (4*(D+1)),eventually_ge_atTop (1:ℝ)] with x bound large one
  have xp:0<x:=zero_lt_one.trans_le one
  have lp:0≤Real.log x:=Real.log_nonneg one
  change ‖Real.log x‖≤1/(4*(D+1))*‖x‖ at bound
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg lp,abs_of_pos xp,one_div,inv_mul_eq_div] at bound
  have out:=(le_div_iff₀ high).1 bound
  nlinarith only [out,large,lp,dp]

include simple in
private theorem room (u : ℕ) {K : ℝ} (kp : 0<K) :
    ∀ᶠ i:ℕ in atTop,K*Real.log (4*(hat! i)) ≤ (C).S.scale i-(C).S.scale u := by
  have slope:=Gauge.slopeConstant_pos simple
  have rate:=Next.Rank.Station.hat_rate (H).levels simple
  have lpos:0≤Real.log 4:=Real.log_nonneg (by norm_num)
  have k0:0≤G.slopeConstant*K*(1+Real.log 4):=by positivity
  filter_upwards [rate.eventually (small k0),rate.eventually_ge_atTop (2*(hat! u))] with i reserved early
  have h:1<(hat! i):=(H).levels.fits.delayed i
  have lp:=Real.log_nonneg h.le
  have logf:Real.log (4*(hat! i))=Real.log 4+Real.log (hat! i):=Real.log_mul (by norm_num) (zero_lt_one.trans h).ne'
  have affine:(hat! i)-(hat! u)=G.slopeConstant*((C).S.scale i-(C).S.scale u):=by
    unfold Calendar.hatBeta
    change _+_*((C).S.scale i)-(_+_*((C).S.scale u))=_
    ring
  apply (mul_le_mul_iff_right₀ slope).1
  rw [←affine,logf]
  have product:=mul_nonneg lpos lp
  have le':Real.log 4+Real.log (hat! i) ≤ (1+Real.log 4)*(1+Real.log (hat! i)):=by linarith
  have fee:=mul_le_mul_of_nonneg_left le' (mul_nonneg slope.le kp.le)
  linarith only [fee,reserved,early]

private theorem last {u i:ℕ} (ui:u ≤ i) {t:ℝ} (tp:0<t)
    (funded:t≤(C).S.scale i-(C).S.scale u) :
    ∃v, u≤v ∧ v < i ∧ t≤(C).S.scale i-(C).S.scale v ∧
      (C).S.scale i-(C).S.scale v<t+Real.log (((C).S.block v).val:ℝ) := by
  let s:Finset ℕ:=(Icc u i).filter fun v=>t≤(C).S.scale i-(C).S.scale v
  have hu:u∈s:=mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,ui⟩,funded⟩
  have sn:s.Nonempty:=⟨u,hu⟩
  let v:=s.max' sn
  have chosen:v∈s:=s.max'_mem sn
  obtain ⟨rangev,ok⟩:=mem_filter.mp chosen
  obtain ⟨uv,vi⟩:=mem_Icc.mp rangev
  have neq:v ≠ i:=by intro h;rw [h,sub_self] at ok;linarith
  have vlt:v < i:=lt_of_le_of_ne vi neq
  have missed:(C).S.scale i-(C).S.scale (v+1)<t:=by
    by_contra! h
    have hmem:v+1∈s:=mem_filter.mpr ⟨mem_Icc.mpr ⟨uv.trans (Nat.le_succ _),Nat.succ_le_of_lt vlt⟩,h⟩
    have too:v+1 ≤ v:=s.le_max' _ hmem
    omega
  rw [Schedule.scale_succ] at missed
  exact ⟨v,uv,vlt,ok,by linarith⟩

include simple in
theorem original (slow : ∀ j, ((C).S.block j).val ≤ Real.log (RG16.Lambda (H).levels j))
    (u d q:ℕ) :
    ∀ᶠ i:ℕ in atTop, ∃ v:ℕ,u≤v ∧ v < i ∧
      (C).S.scale i-(C).S.scale v <
        (8*((q+d+2:ℕ):ℝ))*Real.log (4*(hat! i))+(1+Real.log (hat! i)) ∧
      ∀ N p:ℕ, i<N → let g:=Coat.gStep ((H).rep N p (i+1)).beta
      8*((q+d+2:ℕ):ℝ)*(-Real.log g) ≤ (C).S.scale i-(C).S.scale v ∧
      ∀ E:ℝ,0≤E→8*(1+((H).levels.params i).columns)*(2*(E/g^d)+1)*
        Real.exp (-((C).S.scale i-(C).S.scale v)/8) ≤ 40*(2*E+1)*g^q := by
  let K:ℝ:=8*((q+d+2:ℕ):ℝ)
  have kp:0<K:=by dsimp [K];positivity
  have budget:=WilsonThermometerUnitFilingSchedule.clock R simple slow
  have rise:=RG01.Physical.nextHat simple R.alloy.B.a
  filter_upwards [eventually_ge_atTop u,room R simple u kp,rise,budget] with i ui space next paid
  have hb:1<hat! i:=(H).levels.fits.delayed i
  have lp:0<Real.log (4*(hat! i)):=Real.log_pos (by linarith)
  obtain ⟨v,uv,vi,span,upper⟩:=last R ui (mul_pos kp lp) space
  have logmono : Real.log (hat! v) ≤ Real.log (hat! i) :=
    WilsonAdmissionScale.logarithm_monotone (H).levels simple vi.le
  have L0 : 0<(((C).S.block v).val:ℝ) := by exact_mod_cast ((C).S.block v).pos
  have x0:0<Real.log (hat! v):=Real.log_pos ((H).levels.fits.delayed _)
  have lv:=Real.log_le_sub_one_of_pos (show 0<2+Real.log (hat! v) by linarith)
  have step:Real.log (((C).S.block v).val:ℝ)≤1+Real.log (hat! i):=by
    calc
      _ ≤ (((C).S.block v).val:ℝ) := Real.log_le_self L0.le
      _ ≤ Real.log (RG16.Lambda (H).levels v) := slow v
      _ ≤ _ := by change Real.log (2+Real.log (hat! v))≤_;linarith only [lv,logmono]
  refine ⟨v,uv,vi,upper.trans_le (by linarith only [step]),?_⟩
  intro N p ci g
  have ⟨gp,sg,col⟩:=paid N p ci
  have b0 : 0<((H).rep N p (i+1)).beta := Overlay.beta_positive R.makes.wilson (Nat.succ_le_of_lt ci)
  have band: ((H).rep N p (i+1)).beta ≤ 2*(hat! (i+1)) :=
    (R.makes.wilson.represents N p (i+1) (Nat.succ_le_of_lt ci)).band.2
  have nx : (hat! (i+1)) ≤ 2*(hat! i):=next
  have root:Real.sqrt (((H).rep N p (i+1)).beta) ≤ 4*(hat! i):=by
    have sq:=Real.sq_sqrt b0.le
    nlinarith only [sq,band,nx,hb,sq_nonneg (Real.sqrt (((H).rep N p (i+1)).beta)-1)]
  have logs:-Real.log g≤Real.log (4*(hat! i)):=by
    change -Real.log (Real.sqrt (((H).rep N p (i+1)).beta))⁻¹≤_
    rw [Real.log_inv,neg_neg]
    exact Real.log_le_log (Real.sqrt_pos.mpr b0) root
  have enough: K*(-Real.log g)≤(C).S.scale i-(C).S.scale v:=
    (mul_le_mul_of_nonneg_left logs kp.le).trans span
  refine ⟨enough,?_⟩
  intro E e0
  have cols:0≤((H).levels.params i).columns := by linarith only [((H).levels.params i).columns_ge]
  exact WilsonThermometerUnitFilingSchedule.power gp sg d q cols e0 col enough

end YM.Integration.WilsonThermometerUnitFilingSpan
