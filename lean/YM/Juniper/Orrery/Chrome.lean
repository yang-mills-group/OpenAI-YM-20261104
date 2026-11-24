import YM.Juniper.Orrery.Company
/-!
 # Cutoff step on REAL UV witness under Specs(k) demand, carrying one operator.
 Doesn't require any PARTICULAR scheme interpretation here yet. `Twig`
 all support/error QR via true aux kernels. Ĉ quantities use realized coupling ω
 all stages, never infer "same proof" from another Probe.Regime.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Org Pane Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost Guild Tabernacle Spire
open Poll Pond Blaze Gauze Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {N m n r:ℕ}
variable (U: Nursery G hG)
local notation "S"=> U.S
local notation "A"=> U.A
local notation "H"=> U.A.B.a
local notation "F"=> U.family.path.rep N n
local notation "L"=> U.A.B.a.clock
local notation "T"=> ((U.S).fits N n)
local notation "R"=> U.X
local notation "K"=> (F (m+1)|>.beta)
local notation "G*"=> (F m|>.beta)
local notation "V"=> U.A.B.a.S.side m n
local notation "V₀"=> U.A.B.a.S.side (m+1) n
local notation "Z"=> (L).hatBeta m
local notation "Z₀"=> (L).hatBeta (m+1)
local notation "Y"=> (L).allowance m
local notation "P"=> U.A.B.a.params m
local notation "S₀"=> (L).op m n
local notation "Ψ"=> U.A.B.a.budget m
local notation "B"=> U.A.B.a.budget (m+1)
local notation "Δ"=> (U.A.B.kin.alpha N m)
local notation "J"=> (L).J (m+1)
local notation "I"=> (L).J m
local notation "ε"=> U.S.grove.witness
local notation "Ω"=> (forecastE H m)
local notation "e!"=> Guild.tentPole U.A m (U.S.grove.witness)
abbrev erasureK (a:Levels G)(r m:ℕ):= (rim/8)*(a.clock.hatBeta m ^ r)⁻¹ * a.clock.allowance m
abbrev warmth (a:Levels G)(r m:ℕ):= (a.clock.hatBeta m ^ r)⁻¹
local notation "w"=> (warmth H r m)
local notation "w!"=> (warmth H r (m+1))
local notation "δ"=> ((rim/4)*w)
local notation "δ₀"=> ((rim/4)*w!)
-- stance explicitly in pinned REALITY. budget Y only for posting. Even finite power loss tests input to after; no implicit unresolved charging or hY epoch. Carry kept rep may need per-support rates for T.step etc.
abbrev Year (a : Levels G)(r m:ℕ):= Orrery.Canister G (a.budget m) (a.clock.allowance m) (erasureK a r m)
local notation "A*"=> mount R N m n
-- Output roughly per-size; Earn strong forcing except m=N. At top only know floor!; later obtain more for mark work. Keep eval formula along chain explicitly rather than dropping measures and budget representation.
structure Standing (N m n r:ℕ) (v:Year H r m) (d : Cham H m n)(x y:Valve m n H d)(u:ℝ) : Prop where
    reserved : ‖place H m n d x‖≤rim/2
    climate : ‖place H m n d y‖≤rim/4
    possible : Nonempty (Carved (v.prior (U.A.B.a.S.side m n)).root (v.prior (U.A.B.a.S.side m n)).field (drawer G (U.A.B.a.S.side m n)).reg y.val.1)
    support : x.val.2=y.val.2
    near : ‖place H m n d x-place H m n d y‖ ≤ (rim/4)*warmth H r m
    reads : let p:= mount R N m n x.val ((U.family.path.rep N n m).beta) u
            p.eval=(U.family.path.rep N n m).eval∧ p.Lawful (H|>.params m).width (H|>.params m).paths ((L).loopCap m) ((L).allowance m) ((L).forcedAllowance m)∧ (m<N→p.activities.KBound (H|>.budget m) (Return.forcing U.A.B m))
-- oriented local K owner at all actual
section cash
lemma glow (a:Levels G)(m r:ℕ) : 0 < warmth a r m ∧ 0 ≤ erasureK a r m:= by
    have hz:1 < a.clock.hatBeta m := a.fits.delayed _; have hp:0 ≤ a.clock.allowance m:= (fundedP m a).1.le; unfold erasureK rim warmth; constructor <;> positivity
include hG U
lemma strand : 0 < δ ∧ 0≤e! ∧ 0 ≤ δ₀∧ w! ≤ w:= by
    obtain ⟨hp,hp'⟩:= glow H m r ; obtain ⟨hB,hB'⟩:= glow (H) (m+1) r
    have hξ:0 < ε := U.S.grove.pledge.positive; have hu: ε ≤ Camp.soft := U.S.grove.enabled.charter.hit; have hs:0 < rim:= by norm_num [rim]
    have h : 1 < Z := (H).fits.delayed _
    refine ⟨by positivity,?_,by positivity,?_⟩
    · change 0 ≤ Yard.basisB*Lamppost.Height (U.S.grove.witness) (U.M.p.profile I) G (L|>.hatBeta m)
      rw [← params_eq U.A.B.valid]; apply mul_nonneg Yard.basis_pos; unfold Lamppost.Height; have hv:= Time.credit_pos G P; have hg:(0:ℝ)<δE Z:= (fundedP m H).1; positivity
    exact inv_anti₀ (show 0< Z^r by positivity) (pow_le_pow_left₀ (by linarith only [h]) (le_trans (le_add_of_nonneg_right (b:=G.slopeConstant * Real.log ((H).S.block m|>.val)) (Work.E04.shift_nonneg _ _)) (le_of_eq (Deployment.hat (a:=H) m))) r)
-- avoid invoking Profile shape constants. Independent ε common. CUniform over all N,n,m,r. After table accuracy real coupling. No HB on numerator. At >approach. 
noncomputable def meter : ℝ:= 1+Yard.basisB*4*(U.S.grove.witness)
include U
local notation "λ₁"=> (Ψ).threshold
lemma pricing : Ω ≤ λ₁^2 ∧ e! = (meter U-1)* Ω ∧ 1≤ meter U:= by
    let x:= (L).hatCoupling m; have he:0<x:= Native.sized_pos H m
    have hf:x ≤ 1:= Native.hats_fit H m; have hp:= (fundedP m H).1; have hx:=Time.credit_pos G P
    refine ⟨?_,?_,?_⟩
    · apply (mul_le_of_le_one_left hp.le (Time.authorized G (P)|>.1.trans (by norm_num))).trans; apply le_trans (b:= x^ (2:ℕ)) ?_ ?_; · rw [← Real.rpow_two]; unfold Calendar.allowance; exact Real.rpow_le_rpow_of_exponent_ge he hf (by norm_num)
      exact pow_le_pow_left₀ he.le (show _ from le_mul_of_one_le_right he.le (Real.one_le_exp (sq_nonneg (Real.log (Real.log Z))))) _
    · change Yard.basisB*Lamppost.Height (U.S.grove.witness) (U.M.p.profile I) G (L|>.hatBeta m)=_
      rw [← params_eq U.A.B.valid]; unfold Lamppost.Height forecastE meter; rw [show δE Z= Y from rfl]; ring
    unfold meter; have hA:= Yard.basis_pos; have hξ:= U.S.grove.pledge.positive; exact le_add_of_nonneg_right (by positivity)

-- reset estimate uniform at rank r (lost allowance/(threshold)^2 ≤1).
variable {t a : ℝ}
local notation "C"=> (λ₁)
local notation "L'"=> U.P.L J
local notation "Z₁"=> Gauze.betaK G L' (powerUp r) J Z
local notation "η"=> Ω/(4*Z^J)
local notation "q"=> (rim/8 + rim/4 : ℝ) -- macro typo
include U
lemma saving (h:‖(a:ℝ)‖≤ q * w)(hv:Extol U.P U.X.target U.A.delay)(hk:powerUp r≤ J) (hu:C^2 * |t| ≤ Z₁ + e!*a+η): |t| ≤ (2*rim+(meter U)*q)*w:= by
   obtain ⟨hE,hP⟩:= Voucher.tapP R hv hk; obtain ⟨hf,hh,hζ⟩:=pricing (m:=m) U; have hC:= (Ψ).threshold_pos; have h₀:=glow H m r|>.1; have he:0≤ e! := strand (r:=r) (m:=m) U|>.2.1; have hb:0<Ω:= mul_pos (Time.credit_pos G P) (fundedP m H).1; have hq:0≤ q:= by norm_num [rim]
   have ht:= mul_le_mul_of_nonneg_left ((le_abs_self a).trans h) he; refine le_of_mul_le_mul_left (hu.trans ?_) (sq_pos_of_pos hC); calc
    _ ≤ (2*rim+(meter U)*q)*w*Ω:= by rw [hh] at ht ⊢; linarith only [ht,hE,hP,mul_nonneg (mul_nonneg hq h₀.le) hb.le]
    _ ≤ _ := by rw [mul_comm (C^2)]; exact mul_le_mul_of_nonneg_left hf (by unfold rim; have hp:0 ≤ meter U:= zero_le_one.trans hζ; positivity)
end cash
section orbit
variable (P': Snip G) (V':Extras G) (h:Stock (Orrery.agenda P' V') U)
local notation "h!"=> (Orrery.attaches h).2
local notation "H₀"=> Flare.agenda P' V'
variable (hm:m<N)(hk:powerUp r ≤ U.A.B.a.clock.J (m+1))(hg: Cinch.wraps (U.A.B.a.clock.hatBeta m) (U.A.B.a.S.side m n))
local notation "p!"=> (U.S.fits N n|>.charts m hm)
variable (M:Specs U.A m) (T':Year U.A.B.a r (m+1))(hv:Orrery.Receipt U.X N m (powerUp r) T' M (U.family.path.rep N n (m+1)|>.beta))
variable {d:Cham U.A.B.a (m+1) n}{x y:Valve (m+1) n U.A.B.a d}
   {v:ℝ}(he:Standing U N (m+1) n r T' d x y v)
local notation "u'"=> place H (m+1) n d
local notation "Y'"=> shave (B).B y
local notation "v₀"=> (M.frames (U.A.B.a.S.side m n))
local notation "τ"=> (Averaging.delta ((v₀).book.read (v₀).stamp))
abbrev Pluto : ℝ:= ((meter U)*(rim/8+rim/4)+2*rim)
local notation "λ"=> (Pluto U)
include h hv hk he hG hg hm
local notation "θ₁"=> Orrery.after U.X p! U.S.grove.enabled h! hG M hk
set_option maxHeartbeats 700000 in
lemma major : (|G* - K - Δ - τ| ≤ λ*w) ∧ ∃ d:Cham H m n, ∃ x y:Valve m n H d, ∃ p:ℝ, Standing U N m n r θ₁ d x y p:= by
   obtain ⟨hz,hR⟩:=Orrery.attaches h; obtain ⟨hS',ht⟩:=Flare.boarded P' V' U hz; obtain ⟨ht,hr,hV,hZ,ht',hq⟩:= Voucher.rotation P' V' U hS'
   have hδ:= (Flare.reached P' V' U hz hm hg hk); obtain ⟨hq,hδ⟩:= hδ
   let H':= T'; let e:=Y'; have hp:‖u' x‖ < rim:=he.reserved.trans_lt (by norm_num [rim]); have hf: ‖u' e‖<rim:= (easier y (B).B).trans (he.climate)|>.trans_lt (by norm_num [rim]); obtain ⟨hn,hu⟩:= hδ d (shave _ y) hf; obtain ⟨hz,hΦ,hφ⟩:=Cinch.pristine R hG hm U.S 0 (Spire.Uses.centerP _) (n:=n); have hx:K∈ Rain.lands A m:= hz; have hc:= M.dear; -- unused okay
   let φ₁:=jar R hm T' h! hx; obtain ⟨α⟩:=he.possible
   obtain ⟨hL,b,hU⟩:= Orrery.certify R hm T' h! hx M p! d (shave _ y) (entice α (B).B) hf hn hq
   obtain ⟨⟨d₁,y',x',p,ha,hY,ht,hV,hw,hf',hl,hS⟩,hc⟩:= hu _ _ hL b φ₁ (fun _=>hU) (Orrery.ticks R hm T' h! hx M hv) x v hp he.reads.1
   have hg:=strand (r:=r) (m:=m) U; let q:=(rim/8 + rim/4 : ℝ)
   have hM : Margin (B) (V₀):=wideJ («A»:=A) (U.A.B.a.S.oneStep m n).exact_size h! (by unfold Loft; unfold Bright.home Trio.base Trio.tent at hq; change 100*(1+radiusB Z) ≤ _; omega)
   have hq' : ‖u' x-u' e‖ ≤ q*w:= by
      apply (erased _ y («C»:=α) he.near (T'.erases _ hM) ?_).trans; -- payment defeq?
      · unfold q; rw [add_comm (rim / 4 * _), ← add_mul]; exact mul_le_mul_of_nonneg_left hg.2.2.2 (by norm_num [rim]) -- goal addition type check
      refine mul_nonneg (by norm_num [rim]) ((glow H (m+1) r).1.le)
   rw [show K+ Δ+(G*-(K+ Δ)) = G* from by ring] at hf' hl hS
   refine ⟨?_,d₁,x',y',p,hV,ht,ha,hY.symm,?_, ?_⟩
   · rw [show G*-K-Δ = G*-(K+Δ) from by ring,Pluto,add_comm (meter U*_) (2*rim)] -- rewrite selective
     exact saving U (m:=m) (by simpa only [norm_norm] using! hq') ht' hk hc
   · have hσ:0≤Camp.soft:= by norm_num [Camp.soft,rim]
     have he:0≤w:= (glow H m r).1.le; apply hw.trans; apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hq' (div_nonneg hσ (by norm_num)))).trans; unfold q; simp only [Camp.soft,rim]; unfold warmth at *; linarith only [he]
   exact ⟨hf'.trans (((congr_arg (RG.StepData.push _ K) (he.reads.1))).trans hφ), hS, fun _=>hl⟩ -- push actual symm (hφ : push= F)
end orbit
end YM.Juniper.Orrery
