import YM.RGComparison01.Juncture

/-!
# Fund Weeds and Move dashboard Locality

 For ALL intake, even nearer-model auxiliaries. Further tangent principal
 estimate when `Z` grown to capture its invoices.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Plev
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Height Song
open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open Divides Selector Coin High
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
    {c f : Side} {m N : ℕ} (sizes : f.val=c.val*(A.B.a.S.block m).val)
    (R : Rep G f) (H : Boulevard.Chartlet F.shape A N m sizes R)
local notation "L₀" => D.L (A.B.a.clock.J (m+1))
local notation "Q₀" => F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "sP" => X.p.profile (A.B.a.clock.J m)
local notation "expn" => F.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "θ₀" => A.B.a.clock.hatBeta m
local notation "y" => (A.B.a.params m)
local notation "μ₀" => F.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "S" => (Pane.panel A m sizes)
local notation "T" => (Pane.orchestra A N sizes)
local notation "θv" => betaF G θ₀ L₀
local notation "gZ" => Height.grow G L₀ θ₀
local notation "γ" => A.B.kin.alpha N m
local notation "p" => A.B.a.budget m
local notation "O" => Chi.canonical
local notation "Y₀" => (Beam.marquee H p)
local notation "aH" => (selfA H)
local notation "SI" => (plusone H (aH) O γ)

-- throughout Wet representation

def fromPost (K : Magazine H→Prop) (U : ℝ) : Collection.Source G c :=
    ⟨choir (bySong K O U) ∘ pennant H, (plusone H aH O U).hardRead⟩
lemma post_fee (K : Magazine H→Prop) (U : ℝ) {a : ℝ}
    (h : Meadow.Budget p (Beam.contents H p) (bySong K O U) a) :
    Meadow.Budget p (Y₀).reg (fromPost F sizes R H K U).logRead (turnFee p*a) := Meadow.soared p _ h


variable {R H}

lemma canopy (hm:m<N) (hr : Boulevard.SeekR F.shape A N m sizes H) :
    let Z:=F.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m); let B : ℝ:= θv^(Z.wanting)+θv^(-(7/16):ℝ)
    Collection.Local Y₀ p SI (turnFee p*B) (Coin.wage F m) ∧
     ∀ t : Forest (S).ratio, (S).push R.beta R.eval=earlyValue Y₀ (A.B.kin.path N m) (A.B.a.params m).clip p SI R.beta (weighty H O t) γ := by
  intro Z b
  have hp := F.pledging; let ps:= X.p.profile (A.B.a.clock.J m)
  have hk := hp.agenda _ _ (step_paid A.B.a m)
  have hj: (p).order ≤ ps.order := (congr_arg RG.Stage.order (params_eq A.B.valid m)).le
  have hP: (p).power ≤ ps.power := (congr_arg RG.Stage.power (params_eq A.B.valid m)).le
  have hh : preExponent p ≤ Z.earn := (show preExponent p = ps.supportExponent+3 from congr_arg
    (fun s:RG.Stage=>s.supportExponent+3) (params_eq A.B.valid m)).trans_le hk.1
  let U:=Y₀; have hd:= High.candidate_ok F hm
  have hz (t:Forest (S).ratio) := Boulevard.lays F.shape A sizes aH F.inn.chip hm hp.jewels hp.conducts.full hk.1 hd hr t
  refine ⟨?_,fun t=> by funext V; exact ((hz t).2 V).trans (Beam.travels H p SI _ _ _ V).symm⟩
  obtain ⟨t⟩:= Tree.select (S).ratio (S).patch.odd_side
  obtain ⟨hs,hF,hM,h,hH⟩:=hz t|>.1
  refine ⟨fun i=>Beam.rewrite_rule H p i|>.symm ▸ hs i, ⟨hF.sym,hF.symtest,hF.meas,hF.meas_test,hF.reads,hF.reads_test,hF.permit⟩,?_,?_,hH⟩
  · exact fun u v=>Beam.moves H p O aH u v _
  have hv:= hp.jewels _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  obtain ⟨C,d,v,z,l,g,r,b',q,k,n,⟨Y,hY⟩,hX,hU⟩:= hv.2 _ _ _ T H.laws.data.funds (Pane.ovation A N sizes hm hp.conducts.full) R H
  have he:= Boulevard.suns F.shape A F.inn.chip hm sizes H
  obtain ⟨f,h,hZ⟩:= Meadow.soared p _ (Divides.whole p Y γ rfl rfl hj hP hh hX (A.B.support.cap _ _ hm.le) hd he.1)
  exact ⟨f,fun i=> (hZ i).2,fun i=>budget_loosen (h i) (mul_le_mul_of_nonneg_left (add_le_add hU he.2.1) (turnFee_pos _).le)⟩

/-- Extra timetable. -/
structure Laced (c' d v Y A' b r B q i : ℝ) (k : ℕ) (V : ℕ → ℝ) (t : ℕ) : Prop where
    lets : ∃ N' : Captain H (sP).order c' d v Y A' b r B q k O, Worthy N'.conduit V (gZ ^ High.countOrder t)
    earns : Armada Q₀ L₀ μ₀ (expn).earn θ₀ i B (sP).order k
    norm : collars G i θ₀ (sP).order (sP).power * (salary Q₀ L₀ μ₀ B θ₀ (sP).order k*(1-1/2)⁻¹) ≤ θv ^ (expn).wanting

lemma grants (he : Quests.Gates F.shape A.delay) (hm : m < N)
    {V : ℕ→ℝ} (ht : Tithe.Ticket R.activities R.p V (2*incomingE G L₀ θ₀))
    (k : ℕ) (hk : k ≤ A.B.a.clock.J (m+1)) :
    gZ^High.countOrder k ≤ Real.exp ((Q₀).ε*radiusB θ₀) ∧
    ∃ (c' d v Y A' b r B q i : ℝ) (n : ℕ), Laced F sizes (R:=R) (H:=H) c' d v Y A' b r B q i n V k := by
  obtain ⟨hx,hS⟩:= he _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) k hk
  obtain ⟨c,d,v,Y,k',b,r,B,q,i,n,H,h,hT⟩:= hS _ _ _ T H.laws.data.funds (Pane.ovation A N sizes hm F.pledging.conducts.full) R H V ht
  exact ⟨hx,c,d,v,Y,k',b,r,B,q,i,n,H,h,hT⟩

local notation "assetI" => (Height.asset expn)

-- first orders all periods, no decay in denominator isolated. Weighted.
variable (hm : m < N)
include hm
lemma meter_price (he : Quests.Gates F.shape A.delay) (Ω : ℕ → Prop)
    (k : ℕ) (hk : k ≤ A.B.a.clock.J (m+1)) (hb : R.beta ∈ Shoot.band A.B.a (m+1))
    (seed : gZ ^ High.countOrder k ≤ Real.exp ((Q₀).mark L₀ μ₀ θ₀)) :
    Meadow.Budget p (Y₀).reg (fromPost F sizes R H (Divides.meter H Ω (High.countOrder k) (p).B) γ).logRead
      (2 * (2^k * coupling R.beta^k)) := by
  let g : ℕ → ℝ := fun _=>1
  let B:= p; let x:= θ₀; let v:=θv; let Y:=sP; let E:=expn; let β:=R.beta
  have ht : Tithe.Ticket R.activities R.p g (2*incomingE G L₀ x):= Tithe.no_charge R.activities g (H.laws.data.funds.length_eq ▸ H.laws.intake.cap.labels.boundE) (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (fun _=>rfl)
  obtain ⟨hV,C,d,v',S',k',b,r,B',q,i,n,⟨⟨Hp,hp⟩,hA,hT⟩⟩:= grants F sizes (H:=H) he hm ht k hk
  have hpaid:= step_paid A.B.a m; have hX:=F.pledging
  let σ:= gZ
  obtain ⟨hσ,hψ,hv,hP⟩:= hX.peak.large _ _ hpaid x (A.B.valid.pays m)
  obtain ⟨ha,hR,hΩ⟩:= hP B' i n hA Hp.balance hT
  let ℓ:= High.countOrder k
  have hz := Beacon.spire_weighted Hp hσ g (σ^ℓ) (one_le_pow₀ hσ) ht.1 hp (Y.power) ha hv hR
  let Yf:= A.B.a.clock.loopCap m
  let I : ℝ := collars G assetI x Y.order Y.power * (σ * salary Q₀ L₀ μ₀ B' x Y.order n * (1-1/2:ℝ)⁻¹)
  have hc : y = sP := params_eq A.B.valid m
  have he₁ : (p).order=Y.order:=congr_arg RG.Stage.order hc
  have he₂ : (p).power=Y.power:= congr_arg RG.Stage.power hc
  have hu : preExponent p ≤ (expn).earn := (show preExponent p = Y.supportExponent+3 from congr_arg
    (fun s:RG.Stage=>s.supportExponent+3) hc).trans_le (hX.agenda _ _ hpaid).1
  obtain ⟨hd,hy,_⟩:= Boulevard.suns F.shape A F.inn.chip hm sizes H
  have hpost:= post_fee F sizes R H (Divides.meter H Ω ℓ (p).B) γ
    (Divides.met p Hp g (σ^ℓ) («γ»:=γ) (one_le_pow₀ hσ) ht.1 hσ Ω ℓ (p).B le_rfl rfl rfl he₁.le he₂.le hu seed hV hz
      (A.B.support.cap _ _ hm.le) (High.candidate_ok F hm) hd)
  apply Divides.loosen p hpost
  have hβ  : A.B.a.clock.hatBeta (m+1)=v := PriceCompiler.beta_eq A.B.valid m
  have hpos : 1 ≤ v := hβ ▸ (A.B.a.fits.delayed _).le
  have hσ' : 0 < σ := zero_lt_one.trans_le hσ
  have hε : (Q₀).ε ≤ (y).width/4:= by
    have he:= (Q₀).grants.2.2; rw [hc]; change 8*(Q₀).ε< Y.width at he
    linarith only [he,(Q₀).usable]
  let s:= octaveNeed G p (y).clip (y).width (y).paths Yf β γ
  have hS:s ≤ 1:= hy.trans ((Real.rpow_le_rpow_of_exponent_le hpos (by norm_num : (-(7/16):ℝ) ≤ 0)).trans_eq (Real.rpow_zero _))
  have he₃ : Real.exp (-((y).width/4)*B.B)*s ≤ (σ^ℓ)⁻¹:= by
    apply (mul_le_of_le_one_right (Real.exp_nonneg _) hS).trans
    rw [neg_mul, Real.exp_neg]; apply inv_anti₀ (pow_pos hσ' ℓ)
    exact hV.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)))
  have hd : turnFee p ≤ σ^3:= by
    refine le_trans (turn_price Q₀ hpos p (μ:=μ₀) (k:=n) Hp.balance hA.delta ?_) ?_
    · rw [he₂,he₁]; exact hT.trans ((Real.rpow_le_rpow_of_exponent_le hpos E.arrives.le).trans_eq (Real.rpow_zero _))
    change v ^ (1/2:ℝ) ≤ (v ^ (3/8:ℝ))^3
    calc v ^ (1/2:ℝ) ≤ v ^ ((3/8:ℝ)*(3:ℕ)) := Real.rpow_le_rpow_of_exponent_le hpos (by norm_num)
         _ = _ := by rw [Real.rpow_mul (zero_le_one.trans hpos),Real.rpow_natCast]
  have htr:=turnFee_pos p
  have ht₃ : turnFee p *((σ^3)⁻¹*I) ≤ 1 := by
    have hstep := le_trans (mul_le_mul_of_nonneg_left (show (σ^3)⁻¹ * I ≤ heap G _ (1/16) * δE x from
      (by unfold I; rw [← mul_assoc]; exact hΩ)) htr.le) (c:=1) (b:=turnFee p*(heap G Y (1/16) * δE x))
    apply hstep; rw [heap, ← show turnFee p=away Y from (by unfold turnFee away; rw [he₁,he₂])]
    calc turnFee p * (1/16 * Time.credit G Y /turnFee p * δE x)= 1/16 * Time.credit G Y * δE x:= by field_simp
         _ ≤ _ := by
           have hX : 0 < 1/16 * Time.credit G Y:= mul_pos (by norm_num) (Time.credit_pos ..)
           have H : δE x ≤ 1 := Real.rpow_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _))
             (inv_le_one_of_one_le₀ (show 1 ≤ Real.sqrt x by
               have hv:= Real.sqrt_le_sqrt (A.B.a.fits.delayed m).le; simpa only [Real.sqrt_one] using hv)) (by norm_num)
           nlinarith only [mul_le_of_le_one_right hX.le H, (Time.authorized G Y).1]
  have hδ: turnFee p*((σ^ℓ)⁻¹*I) ≤ (σ^(2*k))⁻¹ := by
    unfold ℓ High.countOrder
    rw [pow_add,mul_inv]
    apply le_trans (b:=(σ^(2*k))⁻¹ * (turnFee p * ((σ^3)⁻¹*I))) (by exact le_of_eq (by ring))
    exact mul_le_of_le_one_right (by positivity) ht₃
  have hK: turnFee p*(Real.exp (-((y).width/4)*B.B)*s) ≤ (σ^(2*k))⁻¹:= by
    apply (mul_le_mul_of_nonneg_left he₃ (by positivity)).trans
    apply (mul_le_mul_of_nonneg_right hd (by positivity : 0≤(σ^ℓ)⁻¹)).trans_eq
    unfold ℓ High.countOrder; rw [pow_add,mul_inv,mul_left_comm, mul_inv_cancel₀ (pow_pos hσ' _).ne',mul_one]
  have hzB : β ≤ 2*v:= hβ ▸ hb.2
  have hF := power_absorb H.laws.intake.positive hpos hzB k
  change turnFee p*((σ^ℓ)⁻¹ * I + Real.exp (-((y).width/4)*B.B)*s) ≤ _
  rw [mul_add,two_mul]
  exact add_le_add (hδ.trans hF) (hK.trans hF)
end YM.RGComparison01.Plev
