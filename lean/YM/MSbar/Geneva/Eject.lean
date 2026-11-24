import YM.MSbar.Geneva.Cycles
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{X f g:ℕ→ℝ}{A:ℕ→Issue G}(hX:Tendsto X atTop atTop) {p m k q:ℕ}
variable (χ:ChartRatio G)(J:Voice G)(H H':Stage)(P:Patch)(D:KernelChoices)
variable (h:G.Simple) (hD:P.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
variable (M:StageCost)(i':G.ColorIndex){b:ℝ} (hp:∀ᶠ i in atTop,Paid (A i) P H H' J (X i)) (hq:∀ᶠ i in atTop,(A i).S.kernel=D)
variable (hc:∀ᶠ i in atTop,Festival (A i) χ p i'∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f i) b∧ Issue.Receipt (A i) M (X i))
variable (hR:∀ᶠ i in atTop, Ore M (X i) P)(h₁:p+2 ≤ m)(ha:Run atTop X f 0)(hk:k=m+1)(hμ:4≤ m)
variable (hv:∀ᶠ i in atTop,k ≤ (A i).post.p.order)(hP:∀ᶠ i in atTop,hatW (tip G P.L (X i))^4 ≤ (A i).f.val)
local notation "Y₀"=>fun i:ℕ=> tip G P.L (X i)
local notation "Q₀" i=> X i
local notation "v₀" i=> vol (Y₀ i)
local notation "W₀" i=> hull (X i)
local notation "Z!" i=> Issue.preModel (A i) χ p
local notation "θ" i=> Meauring.chart (A i).f G
local notation "Λ" i=> ((A i).F)
local notation "Yx" i=> 5*goalP (Y₀ i) p
local notation "α" i=> αm (X i)
local notation "L"=> (P.L.val:ℝ)
variable {C:ℝ}(hK:Ready P M m C) (hσ:3 ≤ M.sway)(hN:6 ≤ M.s)
include hχ hp hq hX h hc hD hQ hR h₁ ha hk hμ hv hP hK hσ hN
omit hv hP hc hD hQ hR h₁ ha hk hμ hK hσ hN hχ hq
lemma shifts : ∀ᶠ i in atTop,1/4≤(A i).shiftClock ∧ (A i).shiftClock ≤ 4:=by
    let v:=Y₀;  have he:Tendsto (fun i=> (Y₀ i)/X i) atTop (𝓝 1):=by
        have he:= (Run.shift hX hX G h P.L 1).2; simpa only [Real.rpow_one] using! he
    filter_upwards [hp,hX.eventually_gt_atTop 0,he.eventually (ge_mem_nhds one_lt_two),he.eventually (le_mem_nhds (by norm_num : (1:ℝ)/2<1))] with i hp hx hh hg
    have hP:= hp.payments.case_; rw [hp.space] at hP; have hv:= hp.payments.hull; let u:= (A i).pre.beta; let w:=(A i).post.beta; have h0:0 < u:= (half_pos (zero_lt_one.trans hP.enough)).trans_le hP.beta; have h1:0 < w:=(half_pos hx).trans_le hv.beta; have hE:w≤16*u ∧ u≤16*w:=by
        have hk:(Y₀ i)≤2*X i:= (div_le_iff₀ hx).mp hh; have hY:1/2*X i≤ (Y₀ i):=(le_div_iff₀ hx).mp hg
        have ha:u≤2*(Y₀ i):=hP.upper; have hp:(Y₀ i)/2≤u:=hP.beta; have hv':X i/2≤w:=hv.beta; have hw': w ≤ 2*X i:=hv.upper; constructor<;> linarith only [hv', hw',hp,ha,hY,hk,hx]
    let a:= Real.sqrt u; let b:= Real.sqrt w; have ha:0<a:=Real.sqrt_pos.mpr h0;have hb:0<b:=Real.sqrt_pos.mpr h1; have hx:a^2=u:=Real.sq_sqrt h0.le; have hh:b^2=w:=Real.sq_sqrt h1.le; change 1/4≤ b⁻¹/a⁻¹ ∧ b⁻¹/a⁻¹≤4; rw [inv_div_inv]; constructor; · rw [le_div_iff₀ hb]; nlinarith only [ha,hb,hx,hh,hE.1]
    rw [div_le_iff₀ hb]; nlinarith only [ha,hb,hx,hh,hE.2]
include hc ha
lemma issuedB :∃ f₀:ℕ→ℝ, Run atTop X f₀ 0∧∀ᶠ i in atTop,1 ≤ f₀ i ∧ 0 ≤ taste p (A i).tilt (A i).cClock ∧ (A i).cClock ≤1∧ Belt p (A i).tilt ≤ f₀ i ∧ Belt p ((A i).tilt)⁻¹≤ f₀ i ∧ 4≤ f₀ i:=by
    let z:ℝ:=((p+1:ℕ):ℝ); have hz:0<z:=by unfold z; positivity
    let g(i):=z*f i; let g'(i):=1+g i; let b(i):=4+|g i|+z*(g' i)^p; have hg:Run atTop X g 0:= ha.mulK hX _; let Wp(i):= (A i).cClock; have hb:= roundS hX J H H' P h hp|>.2.2.1 -- rename
    have hP := hb.bouquet hX (by norm_num); refine ⟨b, ?_,?_⟩; · exact Run.addR hX ((Run.token hX _).addR hX (Run.absA hX hg)) ((((Run.token hX _).addR hX hg).Ypow hX _).mulK hX _)
    filter_upwards [hc, hp,hX.eventually_gt_atTop 0, hP.eventually (ge_mem_nhds zero_lt_one), ((hb.Yrat hX hg).bouquet hX (by norm_num)).eventually (eventually_lt_nhds zero_lt_one)] with i ⟨hc,hK,hB,hG⟩ hp hx ht hL; let s:= (A i).tilt; have hp:0<(A i).post.beta:=(half_pos hx).trans_le hp.payments.hull.beta
    have hg: 1≤ f i:=by have hv:=hB.cast 0 (by omega); rwa [hc.advance,abs_one] at hv
    have h(u:PowerSeries ℝ)(x:ℝ)(he:Bronze.brim p u x):Belt p u ≤ z*x:=(sum_le_sum (s:=range (p+1)) (g:=fun _=>x) (fun i hi=> he i (Nat.lt_succ_iff.mp (mem_range.mp hi)))).trans_eq (by rw [sum_const,nsmul_eq_mul, card_range]); have hv:= h s _ hB.cast; have he:= h s⁻¹ _ (Bronze.cold s hc.advance hB.cast hg); have hi':0 ≤ g i:=(Belt_pos ..).trans hv; have hQ:0 ≤z*(g' i)^p:=mul_nonneg hz.le (pow_nonneg (show 0≤g' i from add_nonneg zero_le_one hi') _); have hf :4 ≤ b i:=by unfold b; linarith only [hQ,abs_nonneg (g i)]
    have hP:Wp i>0:=inv_pos.mpr (Real.sqrt_pos.mpr hp);
    refine ⟨le_trans (by norm_num) hf,?_,ht,hv.trans ?_,he.trans ?_,hf⟩
    · have hx := (sauce s p hP.le ht).trans_lt ((mul_le_mul_of_nonneg_left hv hP.le).trans_lt hL); erw [hc.advance] at hx; linarith only [abs_lt.mp hx|>.1]
    · unfold b; rw [abs_of_nonneg hi']; linarith only [hQ] -- unfold g
    apply le_add_of_nonneg_left (add_nonneg zero_le_four (abs_nonneg _))
omit hp hX h hc ha
lemma flit {G:Gauge}{c:Side}{f:Cacao.Pot (Primary c G)}{p s m:ℕ}{a b v w:ℝ}(he:Tin (Measuring.chart c G) a p s v f b)(hp:w≤v)(hx:0<w): Tin (Measuring.chart c G) a p s w f b:=by refine ⟨he.dec,fun i hi j=>?_⟩; exact (he.fan _ hi _).trans (div_le_div_of_nonneg_left he.dec (pow_pos hx (i+1)) (pow_le_pow_left₀ hx.le hp _))
variable (hn:∀ᶠ i in atTop,hatW (X i)^4 ≤ (A i).c.val)(hY:Kappa m C (1024*b) <1)
include hp hX h hc ha hχ hq hD hQ hR h₁ hk hμ hv hP hK hσ hN hn hY
set_option maxHeartbeats 600000 in
lemma shrinkR : ∀ᶠ i in atTop, let W:=vol (X i); JetTab.RangeB (Measuring.chart (A i).c G) M.s (αm (X i)) W (Issue.filmY (A i) χ p) m (goalP (X i) p)∧ |Issue.shiftClock (A i) - taste p (A i).tilt (A i).cClock| ≤ goalP (X i) p:=by
    obtain ⟨a,ha',hq'⟩:= anchors hX P D H (fun i=>(A i).post) J (fun i=> (A i).Zpost χ) i' p hn (hp.mono (fun i hi=>hi.payments.hull)) (hc.mono fun i he=> ⟨he.1.postT,he.1.pin1⟩) h hQ
    obtain ⟨E,hE,h0⟩:=issuedB hX χ J H H' P h M i' hp hc ha -- order
    have hr:=extension hX χ J H H' P D h hD hQ hχ M i' hp hq hc hR h₁ ha hk hμ hv hP hK hσ hN
    let w(x):=vol (X x); let g(i):= (A i).cClock; let b':=1024*b
    obtain ⟨hh,hF,hG⟩:= Geneva.income hX hE ha (roundS hX J H H' P h hp|>.2.2.1) ha' m p (1/4) b' C
    filter_upwards [hr,h0,hq',hp,hc, shifts hX J H H' P h hp, hh.eventually (ge_mem_nhds hY), hF.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)), hG.eventually (ge_mem_nhds zero_lt_one), hX.eventually_gt_atTop 1,(Alto.broad.comp hX).eventually_ge_atTop 1] with i hr ⟨he,hp0,h1,h2,h3,h4⟩ hq hp ⟨hc,hD,hB,hS⟩ ⟨hs,ht⟩ hκ hh hL hx hpW W
    let Q:=A i; obtain ⟨hT,hpQ⟩:=hc.postC; have hr':0 < w i:=div_pos (zero_lt_one.trans_le hpW) (by positivity); let s:= (A i).shiftClock; have hv:0 < s:=lt_of_lt_of_le (by norm_num) hs; let y:=goalP (X i) p; have hY:0<y:= Real.rpow_pos_of_pos (zero_lt_one.trans hx) _; have hpF:0< Q.pre.beta:=(half_pos (zero_lt_one.trans hp.payments.case_.enough)).trans_le hp.payments.case_.beta;have hg:0< cue Q.pre.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hpF); have hp':0<g i:=by
         unfold g Issue.cClock cue; exact inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans hx)).trans_le hp.payments.hull.beta)); -- c syntax
    let l:=Alto.cWidth (X i); have hα:αm (X i)≤l:=by unfold l αm; rw [_root_.zpow_neg]; unfold Alto.cWidth; rw [one_div]; change ((hatW (X i)^(3:ℕ):ℝ))⁻¹≤((hatW (X i)^2:ℝ))⁻¹; exact inv_anti₀ (pow_pos (zero_lt_one.trans_le hpW) _) (pow_le_pow_right₀ hpW (by norm_num))
    let v':=Alto.flurry (X i); have hw:w i ≤ v':= div_le_self (zero_le_one.trans hpW) (by norm_num); let M':= Measuring.chart Q.c G
    have hP: Tin M' (αm (X i)) M.s m (w i) (ink Q.c Q.post.clip Q.post.path) ((w i)^2*b'):=by
         apply Tin.it hr' (Geneva.flit (m:=m) (Parma.sunrise _ hα _ hB.top) hw hr') (le_of_eq ?_) le_rfl; unfold w vol hatW b'; ring
    have hPower:s⁻¹ ≤ E i:= by apply le_trans (b:=((1:ℝ)/4)⁻¹) (inv_anti₀ (by norm_num) hs); norm_num; exact h4
    obtain ⟨h₁,h₂⟩:=Bristol.appeal Q.post (Q.color χ) Q.tilt s Q.fClock Q.cClock i' hv (div_mul_cancel₀ Q.cClock hg.ne') hr' (show 0<hull (X i) from mul_pos (by norm_num) hr') hpQ.quiet hpQ.bond hpQ.plane hr.2 hr.1 hB.cost hq hS.slope.a0 (by omega : 2≤M.s) (mul_le_mul_of_nonneg_right ht hr'.le) h₁ le_rfl hP (show 0<(1:ℝ)/4 by norm_num) hs hc.advance h2 h3 ((abs_of_nonneg hv.le).le.trans (ht.trans h4)) hPower he hp'.le h1 hp0 (fun i hi=> flit (m:=m) (Parma.sunrise _ hα _ (hB.oak i hi)) hw hr') hh
    exact ⟨ Bristol.runC h₁ ( (div_le_one hY).mp hκ), h₂.trans ((div_le_one hY).mp hL)⟩
end YM.MSbar.Geneva
