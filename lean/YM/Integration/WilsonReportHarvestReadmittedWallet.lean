import YM.Integration.WilsonReportHarvestReadmittedCalendar
import YM.Integration.WilsonReportHarvestReadmittedSource
import YM.Integration.WilsonWindowReportingPace

/-! One before-cutoff bill for the same prescribed physical label at the
actual separating date, with its microscopic normalization unchanged. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReadmittedWallet
open Function Filter Lattice Wilson RG Source Extra.Histories Extraction Spec RG12 RG17
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Harvest
open PhysicalNext.Repeat.Legato WilsonMeasuredAdmission
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta

theorem original (K:ℕ)(hk:0<K)(D h:ℕ)(slow:WilsonWindowReportingPace.Slow R.kit)
    (growing:Tendsto L.level (𝓝[>] (0:ℝ)) atTop)
    (near:∀ᶠr in 𝓝[>] (0:ℝ),(C).S.a (L.level r) ≤ r ∧ r ≤ (C).S.a (L.level r)*(β (L.level r))^2):
    ∀ᶠr in 𝓝[>] (0:ℝ),let m:=WilsonMeasuredWindow.stop A simple K r
      ∀b d N per:ℕ,b ≤ m → max (L.level r) m ≤ N → d ≤ D →
      ∀rail:Rail C,∀B:ℕ→ℕ→ℝ,∀V:Sight C d per,∀U:Emblems C d,
      Spine rail B F.room.cutoff b per d N V U → ∀w:(C).label d,
      mass C d (WilsonReportingUnitOrbit.phase • L.shift d r w) ≤ (β (L.level r))^h →
      let x:=WilsonReportHarvestReadmittedSource.filed L d r w U m N per
      size x ≤ (β m)^(2*(h+1)+2*(K+1))*((C).S.a m/(C).S.a N)^(D+2) ∧
      Many.point U x m N=chunk (WilsonReportingUnitOrbit.primary d)
        (((C).factory d N per).terminal.symm (atRef L d r (N,per) w)) := by
  let M:=(Finset.range (D+1)).sup (C).ref
  have dates:=WilsonMeasuredWindow.stop_tendsto A simple K hk
  filter_upwards [WilsonReportHarvestReadmittedCalendar.original R simple K hk L.level slow.2 growing near,
    growing.eventually (WilsonReportHarvestUpperLabel.paid R simple h),
    dates.eventually (WilsonReportHarvestReadmittedSource.original L),growing.eventually_ge_atTop M]
    with r calendar unscale original age m b d N per begun both degree rail B V U spine w paid x
  have priced:=unscale d (L.shift d r w) paid
  have td:(C).ref d≤L.level r:=(Finset.le_sup (f:=(C).ref)
    (show d∈Finset.range (D+1) from Finset.mem_range.mpr (by omega))).trans age
  have live:m≤N:=(le_max_right ..).trans both
  have alive:L.level r≤N:=(le_max_left ..).trans both
  have bound:=original b d N per rail B V U spine r w td alive begun live
  refine ⟨?_,WilsonReportHarvestReadmittedSource.carried L d r w U m N per live⟩
  let T:=β m
  let T₀:=β (L.level r)
  let a:=(C).S.a m/(C).S.a N
  have temp:2≤T:=calendar.2.2
  have ap:1≤a:=(one_le_div ((C).S.a_pos N)).2 ((C).S.strictAnti.antitone live)
  have T0:0≤T:=by linarith only [temp]
  have q0:0≤T₀:=zero_le_one.trans ((A).fits.delayed _).le
  have large:T₀≤T^2:=(calendar.2.1).trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr temp) T0])
  have mast:WilsonMeasuredAdmission.mast A m≤T^2:=by
    have log:=Real.log_le_sub_one_of_pos (show 0<T by linarith only [temp])
    change 2+Real.log T≤T^2
    nlinarith only [log,temp,sq_nonneg (T-1)]
  have mesh:((C).S.a (L.level r)/(C).S.a m) ≤ (T^2)^(K+1):=
    calendar.1.trans (pow_le_pow_left₀ (mast_pos A m).le mast _)
  have tall:a^(d+2)≤a^(D+2):=pow_le_pow_right₀ ap (by omega)
  have mark:mass C d (((C).S.a (L.level r):ℂ)^d • L.shift d r w)≤(T^2)^(h+1):=
    priced.trans (pow_le_pow_left₀ q0 large _)
  calc size x ≤ a^(d+2)*((C).S.a (L.level r)/(C).S.a m)*mass C d (((C).S.a (L.level r):ℂ)^d • L.shift d r w):=bound
       _ ≤ (a^(D+2)*(T^2)^(K+1))*(T^2)^(h+1):=mul_le_mul
            (mul_le_mul tall mesh (div_pos ((C).S.a_pos _) ((C).S.a_pos _)).le (pow_nonneg (zero_le_one.trans ap) _))
            mark (mass_nonneg ..) (by positivity)
       _ = _:=by rw [←pow_mul,←pow_mul,pow_add];ring

end YM.Integration.WilsonReportHarvestReadmittedWallet
