import YM.Integration.ActualWilsonRootMoment
import YM.OPE.Therm.Bath
import YM.OPE.Therm.Rite

/-! Original Wilson pressure at a fixed fraction of the actual force threshold.
The marked root is kept fixed before the finite period and original cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonHotAllowance
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm
open scoped ENNReal Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {H : History G}
local notation "U" => H.levels
local notation "X" => H.levels.clock.hatBeta
local notation "L" => sigmaU H.levels
local notation "s" => H.S.a
local notation "d" => H.levels.clock.J
variable (Y : Poetry H.levels) (θ : G.Simple)

include Y θ in
theorem window : ∀ᶠ i:ℕ in atTop, ∃ (k:ℕ)(h:k ≤ i), room U k i 2 ∧ ∀ p:ℕ, ((H.S.toDepth h p).count.val:ℝ) ≤ L i^2 := by
    filter_upwards [(log_raised («K»:=U) θ).eventually_gt_atTop 1,(ember_mul («K»:=U) θ 1).eventually (gt_mem_nhds zero_lt_one)] with i hi h
    have hh : L i ≤ X i:= Real.log_le_self (zero_le_one.trans ((U).fits.delayed _).le)
    have hp:s i*X i<1:= by simpa only [Set.mem_Iio,pow_one] using h
    obtain ⟨k,hk,ht,hK⟩:= shelter («K»:=U) i (L i) hi (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh (H.S.a_pos _).le) hp)
    have hf:(d i:ℝ)≥0:= Nat.cast_nonneg _
    have hz:= (Y.stage i).pedestal
    refine ⟨k,hk.le,lt_of_lt_of_le ?_ hK.le,fun p=>?_⟩
    · unfold tail; change 2*(_* ((2:ℕ):ℝ)+_) < _; push_cast; change 100000*((d i:ℝ)+1) ≤ L i at hz; have hh:= H.S.a_pos i
      nlinarith only [mul_le_mul_of_nonneg_right hz hh.le,mul_nonneg hh.le hf, hh]
    have hc:= H.S.embeds_scale (H.S.toDepth hk.le p)
    let a:ℝ := (H.S.block k).val; have ha:0<a:= by unfold a; exact_mod_cast (H.S.block k).pos
    have hM:a ≤ L i := (Y.stage k).track.trans (Real.log_le_log (zero_lt_one.trans ((U).fits.delayed _)) (WilsonStartup.Timing.hat_mono U (Gauge.slopeConstant_pos θ).le hk.le))
    apply le_of_mul_le_mul_left (a:=s i) _ (H.S.a_pos i); rw [hc]; calc
       _ = a*s (k+1):=by rw [H.S.a_step,mul_div_cancel₀ _ ha.ne']
       _ ≤ L i*(L i*s i):= mul_le_mul hM ht (H.S.a_pos _).le (zero_le_one.trans hi.le)
       _ = _:=by ring
include θ in
theorem room_cost {ρ : ℝ} (hρ : 0<ρ) (q : ℕ) :
    ∀ᶠ k in atTop, let l := L k; let M := H.levels.clock.monitor k
      l^10 + (q:ℝ)*M^((1:ℝ)/5) ≤ 5*ρ*M/l := by
  have Ht := Station.hat_rate (U) θ
  have h := (log_raised («K»:=U) θ).eventually_gt_atTop 1
  have hz : 0 < (((q:ℝ)+1)/ρ)^2 := by positivity
  filter_upwards [h,Ht.eventually (curtain 11 ρ 1 hρ zero_lt_one),
    Ht.eventually (curtain 2 1 ((((q:ℝ)+1)/ρ)^2) zero_lt_one hz)] with k hl h₁ h₂
  let l := L k
  let M := H.levels.clock.monitor k
  change 1*l^11≤ρ*M at h₁
  change (((q:ℝ)+1)/ρ)^2*l^2≤1*M at h₂
  change (1:ℝ)<l at hl
  change l^10 + (q:ℝ)*M^((1:ℝ)/5)≤5*ρ*M/l
  have hm : 1≤M := by
    change 1≤Real.exp _
    exact (Real.one_le_exp_iff).2 (sq_nonneg _)
  have hs : (((q:ℝ)+1)/ρ)*l ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    simpa only [mul_pow,one_mul] using h₂
  have Hq : (q:ℝ)*l ≤ ρ*Real.sqrt M := by
    calc
      _ ≤ ((q:ℝ)+1)*l := mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hl.le)
      _ = ρ*((((q:ℝ)+1)/ρ)*l) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hρ.le
  have he : M^((1:ℝ)/5) ≤ Real.sqrt M := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  rw [le_div_iff₀ (zero_lt_one.trans hl),add_mul]
  have h₃ : ((q:ℝ)*M^((1:ℝ)/5))*l ≤ ρ*M := by
    calc
      _ = ((q:ℝ)*l)*(M^((1:ℝ)/5)) := by ring
      _ ≤ (ρ*Real.sqrt M)*Real.sqrt M :=
        mul_le_mul Hq he (Real.rpow_nonneg (zero_le_one.trans hm) _) (by positivity)
      _ = ρ*M := by rw [mul_assoc,←sq,Real.sq_sqrt (zero_le_one.trans hm)]
  have h₄ : l^10*l≤ρ*M := by simpa only [pow_succ,one_mul] using h₁
  nlinarith only [h₃,h₄,mul_nonneg hρ.le (zero_le_one.trans hm)]

include Y θ in
/-- One actual rooted hot plaquette pays every fixed power of the original force allowance. -/
theorem face (Z : H.Selected) {ρ : ℝ} (hρ : 0<ρ) (q : ℕ) :
    ∀ᶠ k in atTop, ∀ N,k≤N → ∀ per (z : Face (Per (H.S.side k per))),
      (scene H N per k).real (trigger z (ρ*(H.rep N per k).p.threshold)) ≤
        H.levels.clock.forcedAllowance k ^ q := by
  filter_upwards [window Y θ,Vac.treasury_stage U θ,
    (log_raised («K»:=U) θ).eventually_gt_atTop 100,narrow (H:=H) θ,
    room_cost (H:=H) θ hρ q] with k ⟨i,hk,hE,hi⟩ hv hh hτ hcost N hN per z
  obtain ⟨x,t⟩ := z
  rw [displaced Z hN]
  let b := X k
  let l := L k
  let M := H.levels.clock.monitor k
  let g := H.levels.clock.hatCoupling k
  let R := H.rep N per k
  let u := gap R.beta
  let c := strength ((U).params k).clip
  let Q : ℝ := (H.S.toDepth hk per).count.val
  let a := Vac.treasury U k + Fintype.card PlaqAxes
  have own := Z.represents N per k hN
  have hb : 1<b := (U).fits.delayed _
  have hβ : 0<R.beta := by refine lt_of_lt_of_le ?_ own.band.1; linarith only [hb]
  have hu : 0<u := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hb))
  have beat : u≤2*g := (band_gap b _ (zero_lt_one.trans hb) (trial_in own.band)).2
  have hl : (100:ℝ)<l := hh
  have hl' : 1≤l := by linarith
  have hM : 0<M := Real.exp_pos _
  have hν : R.beta*u^2=1 := by
    dsimp [u,gap]
    field_simp
    exact (Real.sq_sqrt hβ.le).symm
  have hmask : R.p.threshold=g*M := by
    change (H.rep N per k).p.threshold=_
    rw [own.vac]
    rfl
  have small : u≤R.p.threshold := by
    apply beat.trans
    change _ ≤ (H.rep N per k).p.threshold
    rw [own.vac]
    apply le_trans ?_ hτ.2
    unfold cool
    change 2*g≤4*(g*l^12)
    nlinarith only [one_le_pow₀ (n:=12) hl',hg]
  have hA : Q^4*a ≤ l^10 := by
    have hx : a≤l^2 := (add_le_add_left hv _).trans ((Y.stage k).price)
    exact ((mul_le_mul_of_nonneg_left hx (pow_nonneg (by change 0≤Q; unfold Q; positivity) _)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by change 0≤Q; unfold Q; positivity) (hi per) 4)
        (sq_nonneg _))).trans_eq (by ring)
  have hc : 0<c := strength_pos _
  have line : 10≤c*l := by
    rcases le_total 1 ((U).params k).clip.linear with h|h
    · rw [show c=1 from min_eq_left h,one_mul]
      linarith
    rw [show c=_ from min_eq_right h]
    have he := (div_le_iff₀ ((U).params k).clip.tail_pos).1 (Y.stage k).strain
    simpa only [l,sigmaU,mul_comm] using he
  have hl0 : 0<l := zero_lt_one.trans_le hl'
  have head : 5*ρ*M/l ≤ (ρ*R.p.threshold)/(u/c) := by
    rw [hmask,div_div_eq_mul_div,le_div_iff₀ hu]
    calc
      _ ≤ (5*ρ*M/l)*(2*g) := mul_le_mul_of_nonneg_left beat (by positivity)
      _ ≤ (ρ*(g*M))*c := by
        apply (mul_le_mul_iff_of_pos_right hl0).mp
        calc
          ((5*ρ*M/l)*(2*g))*l = (ρ*(g*M))*10 := by field_simp; ring
          _ ≤ (ρ*(g*M))*(c*l) := mul_le_mul_of_nonneg_left line (by positivity)
          _ = _ := by ring
  have Hp := away (p:=per) (τ:=ρ*R.p.threshold) Z hk hN t hE hu small hν
  rw [Calendar.forcedAllowance,← Real.exp_nat_mul]
  apply Hp.trans (Real.exp_monotone ?_)
  change Q^4*a-(ρ*R.p.threshold)/(u/c) ≤ (q:ℝ)* -M^((1:ℝ)/5)
  change l^10+(q:ℝ)*M^((1:ℝ)/5)≤5*ρ*M/l at hcost
  linarith only [hA,head,hcost]

include Y θ in
/-- All original fields may have arbitrary exterior flags. The number of named
plaquettes is the only support multiplicity in this paid thermal event. -/
theorem faces (Z : H.Selected) {ρ : ℝ} (hρ : 0<ρ) (q : ℕ) :
    ∀ᶠ k in atTop, ∀ N,k≤N → ∀ per (J : Finset (Face (Per (H.S.side k per)))),
      (scene H N per k).real ((House.chilly J (ρ*(H.rep N per k).p.threshold))ᶜ) ≤
        J.card * H.levels.clock.forcedAllowance k ^ q := by
  filter_upwards [face Y θ Z hρ q] with k h N hN per J
  letI := probability (p:=per) Z hN
  exact House.cool_miss _ (h N hN per) J

end YM.Integration.PhysicalWilsonHotAllowance
end
