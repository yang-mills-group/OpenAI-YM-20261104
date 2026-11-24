import YM.RGComparison01.Coin

/-!
# High tail on the Roost construction

The early, *pre-reset* unmarked `Song` output (an actual represented
push, including the `receipt`). Full-point evaluation, and prices in
that representation. Still need exposure and comparison of the retained
low entries. `Sel` threshold is pre-orientation. Order cuts are not
claims of an analytic disk for varying actual `β`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Song
open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace High
open LogSplit Height Coin

/-- Internal degree cut, can pay high part to `g^q`. -/
def countOrder (q : ℕ) := 2*q + 3

-- keep common representation format visible also on auxiliary sides
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
    {c f : Side} {m N : ℕ} (sizes : f.val=c.val*(A.B.a.S.block m).val)
    (R : Rep G f) (H : Boulevard.Chartlet F.shape A N m sizes R)
local notation "L₀" => D.L (A.B.a.clock.J (m+1))
local notation "Q₀" => F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "expn" => F.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "θ₀" => A.B.a.clock.hatBeta m
local notation "μ₀" => F.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "θv" => betaF G θ₀ L₀
local notation "γ" => A.B.kin.alpha N m
local notation "p" => A.B.a.budget m
local notation "O" => Chi.canonical
local notation "Sel" => Beacon.Exceptional H

-- pre-reset regular receipt
include F in
lemma candidate_ok (hm : m<N) : WilsonStartup.Decent (A.B.a.params m).clip p := by
  let u:= A.B.a.params m
  have hp:= F.machine.shops _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have he:= params_eq A.B.valid m
  have hQ:= Deployment.clock_eqns A.B.a.clock m
  have hi: Same u p:= ⟨rfl,rfl,rfl⟩
  have hx:= (hp (A.B.a.budget m) (show Same _ _ from he ▸ hi) rfl hQ.2.2.2.2.2.2).1
  rw [← he] at hx; exact hx (Canonical.direct_le_one (A.B.support.cap N m hm.le).metric)

abbrev selfAlliance := Match.staple (H:=H) (J:=H) rfl rfl rfl

theorem height_budget (hm : m < N) (k : ℕ) (hb : R.beta ∈ Shoot.band A.B.a (m+1))
    (hd : WilsonStartup.Decent (A.B.a.params m).clip p)
    (seed : Height.grow G L₀ θ₀ ^ countOrder k ≤ Real.exp ((Q₀).mark L₀ μ₀ θ₀)) :
    Meadow.Budget p (posting p H).reg
      (LogSplit.selected (selfAlliance F sizes R H) (Beacon.Exceptional H (countOrder k)) O γ
        (countOrder k*Pressure.Stores.till θ₀)).logRead
      (2 * (2^k * coupling R.beta^k)) := by
  let L:= L₀; let y := θv; let C:= A.B.a.clock; let Q := Q₀
  let x := θ₀; let u:= A.B.a.params m; let hi:= C.J (m+1); let lo:= C.J m; let expN := expn
  let α := γ; let β:= R.beta; let P:= p
  let Z:=Height.grow G L θ₀
  let l:= countOrder k
  let W:= Pane.orchestra A N sizes
  have hstage:= step_paid A.B.a m
  have hpay:= A.B.valid.pays m
  have hz:= F.pledging.jewels hi x hpay lo hstage
  obtain ⟨C',d,v,t,Y,b,r,B,q,i,k',⟨K,hheavy⟩,hK,hKpay⟩ := hz.2 _ _ _ W H.laws.data.funds
    (Pane.ovation A N sizes hm F.pledging.conducts.full) _ H
  obtain ⟨hH,hseed₃,hV,hY⟩ := F.pledging.peak.large hi lo hstage x hpay
  obtain ⟨ha,hv,h₀⟩ := hY B i k' hK K.balance hKpay
  let j:= (X.p.profile lo).order; let n:= (X.p.profile lo).power; let w:=asset expN
  let I : ℝ := collars G w x j n * (Z * salary Q L μ₀ B x j k' * (1-1/2:ℝ)⁻¹)
  have hy : A.B.a.clock.hatBeta (m+1)=y:= PriceCompiler.beta_eq A.B.valid m
  have hs : 1≤y:= hy ▸ (A.B.a.fits.delayed _).le
  have hS : 0 < β:= (by change C.hatBeta (m+1)/2 ≤ β ∧ _ ≤ _ at hb; exact (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))).trans_le hb.1)
  have hZ : 0 < Z := zero_lt_one.trans_le hH
  have hI : Ac.Hit Captain.reachability (radiusB θ₀) (fun z => if Sel l z then K.markΦ z n else 0)
      expN.earn ((Z^l)⁻¹ * I) := Beacon.recover K (Sel l) (pow_pos hZ _)
    (Beacon.cashout hH seed hz.1) (Beacon.weighted K hH hheavy n ha hV hv)
  have hr := (F.pledging.agenda hi lo hstage).1
  have hc : u=X.p.profile lo := params_eq A.B.valid m
  have hp : P.power=n:= congr_arg RG.Stage.power hc
  have hj : P.order=j:= congr_arg RG.Stage.order hc
  have ht' : preExponent P ≤ expN.earn := (show preExponent P = (X.p.profile lo).supportExponent+3 from
    congr_arg (fun s:RG.Stage=>s.supportExponent+3) hc).trans_le hr
  have ht:= A.B.support.cap N m hm.le
  obtain ⟨hh,h',hω⟩ := Boulevard.suns F.shape A F.inn.chip hm sizes H
  obtain ⟨g,hg,h⟩ := selected_budget p (selfAlliance F sizes R H) (Sel l) K γ (l*Pressure.Stores.till θ₀) rfl rfl hj.le hp.le ht' hI ht hd hh
  refine ⟨g,fun x => budget_loosen (hg x) ?_,h⟩
  let Cx := forecastE A.B.a m
  have hT := turnFee_pos P
  have hx : 1/16 * Cx ≤ 1 := by
    have hy : 0 ≤ θ₀ := (zero_lt_one.trans (A.B.a.fits.delayed m)).le
    have hw : C.allowance m ≤ 1 := Real.rpow_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_le_one_of_one_le₀ (show 1 ≤ Real.sqrt θ₀ by
        have hv:= Real.sqrt_le_sqrt (A.B.a.fits.delayed m).le; simpa only [Real.sqrt_one] using hv)) (by norm_num)
    have ht:= Time.credit_pos G u
    have hX : Cx ≤ 1/64*1 := mul_le_mul (by simpa only [one_div] using (Time.authorized G u).1) hw
      (by unfold Calendar.allowance Calendar.hatCoupling; positivity) (by norm_num)
    linarith
  have hw : turnFee P * ((Z^3)⁻¹ * I) ≤ 1 := by
    have hc0 : (Z^3)⁻¹ * I ≤ heap G (X.p.profile lo) (1/16) * δE θ₀:= by rw [← mul_assoc]; exact h₀
    apply (mul_le_mul_of_nonneg_left hc0 hT.le).trans
    apply le_trans _ hx
    apply le_of_eq
    rw [heap, ←hc]
    have he : away u=turnFee P:= rfl
    rw [he]; change _=1/16*(Time.credit G u * δE θ₀)
    field_simp
  let V:= octaveNeed G P u.clip u.width u.paths (C.loopCap m) β γ
  have hbound : V ≤ 1:= h'.trans ((Real.rpow_le_rpow_of_exponent_le hs (by norm_num : (-(7/16):ℝ) ≤ 0)).trans_eq
    (Real.rpow_zero _))
  have hε : Q.ε ≤ u.width/4:= by
    have he:= Q.grants.2.2; rw [hc]; change 8*Q.ε< (X.p.profile lo).width at he
    linarith only [he,Q.usable]
  have hf : Real.exp (-(u.width/4)*(l*Pressure.Stores.till θ₀ : ℕ)) ≤ (Z^l)⁻¹ := by
    rw [neg_mul,Real.exp_neg]; apply inv_anti₀ (pow_pos hZ l)
    have hu : Z ≤ Real.exp (Q.ε * Pressure.Stores.till θ₀):= (le_self_pow₀ hH (by decide)).trans hz.1
    apply (pow_le_pow_left₀ hZ.le hu l).trans
    rw [← Real.exp_nat_mul]; apply Real.exp_monotone
    push_cast
    linarith only [mul_le_mul_of_nonneg_right hε (by positivity : 0 ≤ (l:ℝ)* Pressure.Stores.till θ₀)]
  have hturn : turnFee P ≤ Z^3:= by
    apply le_trans (turn_price Q hs P (μ:=μ₀) (k:=k') K.balance hK.delta ?_)
    · change y ^ (1/2:ℝ) ≤ (y ^ (3/8:ℝ))^3
      calc y ^ (1/2:ℝ) ≤ y ^ ((3/8:ℝ)*(3:ℕ)) := Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
           _ = _ := by rw [Real.rpow_mul (zero_le_one.trans hs),Real.rpow_natCast]
    rw [hp,hj]
    apply hKpay.trans
    exact (Real.rpow_le_rpow_of_exponent_le hs expN.arrives.le).trans_eq (Real.rpow_zero _)
  have hV : Real.exp (-(u.width/4)*(l*Pressure.Stores.till θ₀ : ℕ))* V ≤ (Z^l)⁻¹ :=
    (mul_le_of_le_one_right (Real.exp_nonneg _) hbound).trans hf
  have hE : turnFee P*((Z^l)⁻¹ * I) ≤ (Z^(2*k))⁻¹ := by
    change turnFee P*((Z^(2*k+3))⁻¹ * I) ≤ _
    rw [pow_add, mul_inv]
    calc _ = (Z^(2*k))⁻¹ * (turnFee P * ((Z^3)⁻¹*I)) := by ring
         _ ≤ _ := mul_le_of_le_one_right (by positivity) hw
  have hL : turnFee P*(Real.exp (-(u.width/4)*(l*Pressure.Stores.till θ₀ : ℕ))*V) ≤ (Z^(2*k))⁻¹:= by
    apply (mul_le_mul_of_nonneg_left hV hT.le).trans
    apply (mul_le_mul_of_nonneg_right hturn (by positivity : 0≤(Z^l)⁻¹)).trans_eq
    unfold l countOrder; rw [pow_add,mul_inv,mul_left_comm, mul_inv_cancel₀ (pow_pos hZ _).ne',mul_one]
  have hzB : β ≤ 2*y:= hy ▸ hb.2
  have hR := power_absorb hS hs hzB k
  change turnFee P*((Z^l)⁻¹ * I + Real.exp (-(u.width/4)*(l*Pressure.Stores.till θ₀ : ℕ))* V) ≤ _
  rw [mul_add,two_mul]
  exact add_le_add (hE.trans hR) (hL.trans hR)

/- One precise tail clause. No mark insertions here. Auxiliary-calendar formulation
works on general period sides too; physical adapter in PhysicalHigh. -/
def PreReset (k : ℕ) : Prop :=
  let Y := (selfAlliance F sizes R H)
  let Z := posting p H
  let P := plusone H Y O γ
  let M := Coin.wage F m
  let g := Coin.coupling R.beta
  let w := A.B.a.clock.forcedAllowance m
  let ℓ := countOrder k
  let δ := 2 * (2^k * g^k)
  let K := ℓ * Pressure.Stores.till θ₀
  let V₀ := LogSplit.kept Y (Beacon.Exceptional H ℓ) O γ K
  let V₁ := LogSplit.selected Y (Beacon.Exceptional H ℓ) O γ K
  Collection.Local Z p P
    (turnFee p * (θv ^ (expn).wanting + θv ^ (-(7/16) : ℝ))) M ∧
    Meadow.Budget p Z.reg V₁.logRead δ ∧ (Z.read V₁).EBound p δ ∧ (Z.read P).KBound p M ∧
    M ≤ (1/8 : ℝ) * Time.forecastK A.B.a m F.scout R.beta ∧
    M ≤ Real.sqrt w * g ^ k ∧
    ∀ t : Tree.Forest (Pane.panel A m sizes).ratio,
      (Pane.panel A m sizes).push R.beta R.eval =
        earlyValue Z (A.B.kin.path N m) (A.B.a.params m).clip p P R.beta (weighty H O t) γ ∧
      (∀ V, earlyValue Z (A.B.kin.path N m) (A.B.a.params m).clip p P R.beta (weighty H O t) γ V =
        earlyValue Z (A.B.kin.path N m) (A.B.a.params m).clip p V₀ R.beta (weighty H O t) γ V *
          Real.exp (- (Z.read V₁).additive p V))

lemma pays (hm : m < N) (k : ℕ) (hb : R.beta ∈ Shoot.band A.B.a (m+1))
    (hv : Boulevard.SeekR F.shape A N m sizes H)
    (hs : Height.grow G L₀ θ₀ ^ countOrder k ≤ Real.exp ((Q₀).mark L₀ μ₀ θ₀))
    (hk : Coin.wage F m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m) * Coin.coupling R.beta ^ k) :
    PreReset F sizes R H k := by
  let Y:=selfAlliance F sizes R H
  let Z:= posting p H
  have hr := F.pledging
  have ha:= candidate_ok F hm
  let V:= plusone H Y O γ
  have hz (t : Tree.Forest (Pane.panel A m sizes).ratio) := Boulevard.lays F.shape A sizes Y F.inn.chip hm hr.jewels
    hr.conducts.full (hr.agenda _ _ (step_paid A.B.a m)|>.1) ha hv t
  obtain ⟨t⟩ := Tree.select (Pane.panel A m sizes).ratio (Pane.panel A m sizes).patch.odd_side
  have hy := (hz t).1
  have hR := height_budget F sizes R H hm k hb ha hs
  obtain ⟨u,h,hF⟩:= hy.expensive
  refine ⟨hy,hR, LogSplit.unweighted p hR,
    ⟨u,h,Payments.drop_reserve p _ (fun i => (h i).1) hF⟩,?_,hk,
    fun t => ⟨funext (hz t|>.2),LogSplit.reconstruct p Y _ O γ _ hy hR (weighty H O t)⟩⟩
  unfold Coin.wage Time.forecastK
  rw [PriceCompiler.beta_eq A.B.valid]
  exact hr.conducts.income.earns _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) _ (PriceCompiler.beta_eq A.B.valid m ▸ trial_in hb)

/-- Supplied analytic/vacuum tail before reexpression. Uniform even with
unbounded periods, not necessarily meshes of the actual history, whenever
the actual component construction works with its usual renewals and
same path/coupling setting. `SeekR` isn't the perturbative bound being
proved. --/
theorem eventually_pays (hG : G.Simple) (k : ℕ) : ∀ᶠ m in atTop,
    ∀ (N : ℕ), m<N → ∀ (c f : Side) (sizes : f.val=c.val*(A.B.a.S.block m).val)
      (I : RG.Rep G f), I.beta ∈ Shoot.band A.B.a (m+1) →
        ∀ (H : Boulevard.Chartlet F.shape A N m sizes I), Boulevard.SeekR F.shape A N m sizes H →
          PreReset F sizes I H k := by
  filter_upwards [Coin.seeds_paid F hG (countOrder k),Coin.forced_price F hG k] with m hm hv
  intro N hn c f sizes I hI H hh
  exact pays F sizes I H hn k hI hh hm (hv _ hI)
end High
end YM.RGComparison01
