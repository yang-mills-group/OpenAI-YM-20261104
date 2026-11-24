import YM.Integration.WilsonThermometerWeakGroupCoupon

/-! The regulator-uniform group aperture bill for the displaced field's actual group
polynomial. The cutoff and period are chosen after the physical reporting threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGroupTariff
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerWeakTaylor WilsonThermometerWeakPrimary
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} (C:Family G)
variable {d D k N p b m:ℕ}

private theorem mass {n:Side} {ι:Type*} {S:Rules G} {P:BudgetPoint}
    {Z:ι→Support n} {A:ι → Config G n → ℂ} {f:ι→ℂ}
    {q:poly (links G (0:Site n) b)} {rent H cash:ℝ}
    (h:Summary S P b D Z A f rent cash q) (hr:0≤rent) (hm:rent≤H):
    0≤cash ∧ coin q≤cash*H := by
  obtain ⟨e,ce,T⟩:=h
  have h0:0≤cash:=(tsum_nonneg ce.1).trans ce.2.2
  exact ⟨h0,T.charge.trans ((mul_le_mul_of_nonneg_right ce.2.2 hr).trans (mul_le_mul_of_nonneg_left hm h0))⟩

theorem original (simple:G.Simple) (laws:C.Makes) (S:Rules G) (D:ℕ) :
    ∀ᶠ k:ℕ in atTop,∀ N (_:k≤N) p,
    let P:=C.path.rep N p k
    let n:=sizeQ C k
    let m:=scouts C k
    let s:=clim C.path.levels k
    ∀ {d:ℕ} (K:Provision C d k N p m n) (X:Coefficient (C.labels.level d) (C.side k p)),
    X.Format 0 C.params P →
    ∀ {q u v:poly (Up C k p n)} {a e cap cash:ℝ},0≤a → a≤tin s D→0≤e→e≤tin s D→
    Summary S P.p n D (verseX C d k p) (verseA C d k p) (weights C P.p.threshold X.x) a cap q →
    Summary S P.p n D (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e cash u →
    Summary S P.p n D (fun j:Far (P:=P) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e (expCut P.p m*cash) v →
    ∀ U:Config G (C.side k p),Healthy (tau C.path.levels k) (Spindle.patch n 0) U →
    ‖X.exponentialEntry 0 (C.localSection d) P U-
      signet 0 (GaugeScale C k N p) (sender K.length P.p.threshold (GaugeScale C k N p) (q+(u+v))) U‖
      ≤(cap+cash)*bill (-(D:ℝ)) s := by
  let e₀:=shade D
  let y:=-(D:ℝ)-3
  let J:=hat_rate C.path.levels simple
  have hs:(-1+e₀)*((D:ℝ)+1)< -(D:ℝ) := by
    have h:=shade_thin D;have hp:0<e₀:=shade_pos D;dsimp [e₀] at *;linarith only [h,hp]
  have hs':e₀+y< -(D:ℝ) :=by dsimp [e₀,y];linarith only [shaded D]
  have yy:y< -(D:ℝ):=by dsimp [y];linarith
  filter_upwards [radius_paid C (shade_pos D) simple laws,iced S C simple laws y,
    shrank C (-y) simple laws,J.eventually (hotter 1 zero_lt_one),
    J.eventually (transports hs 6),J.eventually (transports yy 6),
    J.eventually (transports hs' (6*D))] with k radius ice long hot c₁ c₂ c₃
    N hn p P n m s d K X form q u v a e cap cash ap ar ep er hq hu hv U healthy
  let W:=q+(u+v)
  let M:=tin s D
  let τ:=tau C.path.levels k
  let t:=P.p.threshold
  let R:=4*(n:ℝ)*τ
  let r:=2*R/t
  let w:=(S.C+G.colorScale)*R^2/t
  let b:=bill (-(D:ℝ)) s
  let f:=expCut P.p m
  have ht:P.p.threshold=C.path.levels.clock.threshold k:=by rw [(laws.wilson.represents N p k hn).vac];rfl
  have ht':τ≤t := by
    dsimp only [t];rw [ht];change C.path.levels.clock.hatCoupling k*Perch.hot s≤
      C.path.levels.clock.hatCoupling k*C.path.levels.clock.monitor k
    have hm:bill 1 s=C.path.levels.clock.monitor k:=by unfold bill;rw [mul_one];rfl
    exact mul_le_mul_of_nonneg_left (hot.trans_eq hm) (le_of_lt (inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (C.path.levels.fits.delayed k)))))
  have rg:0≤r:=by dsimp [r,R,t];have:=tau_pos C.path.levels k;have:=P.p.threshold_pos;positivity
  have ib : Ice S R t ∧ w≤bill y s := by simpa only [t,w,ht] using ice
  have rr:r≤bill (-1+e₀) s:= by simpa only [r,t,ht] using radius
  have rp:r^(D+1)≤bill ((-1+e₀)*((D:ℝ)+1)) s:= by
    apply (pow_le_pow_left₀ rg rr _).trans_eq
    rw [bills];push_cast;rfl
  have f0:0≤f:=(Real.exp_pos _).le
  have f1:f≤1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr P.p.exponent_pos.le) (Nat.cast_nonneg _))
  have hf:f≤bill y s:=by simpa only [neg_neg] using long N hn p
  have g0:0<GaugeScale C k N p:=inv_pos.mpr (Real.sqrt_pos.2 (Overlay.beta_positive laws.wilson hn))
  have raw:=WilsonThermometerWeakGroupCoupon.original S K X form hq hu hv g0 (tau_pos _ _) ht' U healthy ib.1.1 ib.1.2.1 ib.1.2.2
  obtain ⟨cp,qc⟩:=mass hq ap ar
  obtain ⟨cr,uc⟩:=mass hu ep er
  obtain ⟨_,vc⟩:=mass hv ep er
  have M0:0≤M:=(Real.exp_pos _).le
  let E:=cap+cash
  have E0:0≤E:=add_nonneg cp cr
  have fpaid:f*cash≤E:=(mul_le_of_le_one_left cr f1).trans (le_add_of_nonneg_left cp)
  have A:cap+cash+f*cash≤2*E:=by dsimp [E] at *;linarith only [fpaid]
  have Wpaid:coin W≤(2*E)*M :=
    (taller 0 zero_le_one _ _).trans ((add_le_add qc ((taller 0 zero_le_one _ _).trans (add_le_add uc vc))).trans
      ((le_of_eq (by ring : cap*M+(cash*M+f*cash*M)=(cap+cash+f*cash)*M)).trans
        (mul_le_mul_of_nonneg_right A M0)))
  have c1:6*r^(D+1)≤b:=(mul_le_mul_of_nonneg_left rp (by norm_num : (0:ℝ)≤6)).trans c₁
  have c2:6*f≤b:=(mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ)≤6)).trans c₂
  have c3:6*(D:ℝ)*M*w≤b := by
    refine (mul_le_mul_of_nonneg_left ib.2 (by positivity : 0≤6*(D:ℝ)*M)).trans ?_
    rw [mul_assoc,show M=bill e₀ s from rfl,overlap]
    exact c₃
  have w0:0≤w:= by dsimp [w,t];have:=S.positive;have:=G.colorScale_pos;have:=P.p.threshold_pos;positivity
  change _≤E*b
  apply raw.trans
  change (cap+cash+f*cash)*r^(D+1)+2*(f*cash)+coin W*(D*w)≤_
  have e1:=mul_le_mul_of_nonneg_right A (pow_nonneg rg (D+1))
  have e2:2*(f*cash)≤2*(f*E) := by gcongr;exact le_add_of_nonneg_left cp
  have e3:=mul_le_mul_of_nonneg_right Wpaid (mul_nonneg (Nat.cast_nonneg D) w0)
  linarith only [e1,e2,e3,mul_le_mul_of_nonneg_left c1 E0,mul_le_mul_of_nonneg_left c2 E0,
    mul_le_mul_of_nonneg_left c3 E0]

end YM.Integration.WilsonThermometerWeakGroupTariff
end
