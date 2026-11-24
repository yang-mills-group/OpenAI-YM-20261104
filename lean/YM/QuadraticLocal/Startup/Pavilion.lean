import YM.QuadraticLocal.Startup.Headway
import YM.QuadraticLocal.Germ.Entrance
import YM.QuadraticLocal.Startup.Morning
/-!
# Startup and tall-term Book across the stepped ACTUAL path

 Reach: full TestSpace operations & post coupling all. Periods after shape handshake. Reuse
 any Concourse (prepay slack & exact Advance) including at b = N terrace. Installation takes seats
 at any b which will be reading X. Every force recovery paid enough kernel power even at input,
 not smaller assumption ahead. Fresh rail for globals in companion file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
local notation "κ'"=> forcedDivisor Z i
open Travel
variable (hP: AllOrder.Transit.WheelP.Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
namespace Uplink
open QuadraticLocal.Hard QuadraticLocal.Spes QuadraticLocal.Kiosk Marker Spes.Market ComparisonDensity.Address
private lemma dummy {K: Marker.Census PUnit.{1}} (x:K.Mode): x.val.card≤1:= by simpa using Finset.card_le_univ x.val
private def Kes : Marker.Census PUnit.{1} := ⟨Finset.univ,Finset.mem_univ _,fun _=>Finset.mem_univ _,fun _ _ _=>Finset.mem_univ _⟩
private def empty {n:Side}{V:Type}[DecidableEq V]{T: Marker.Census V}{o:V→Site n}{p:BudgetPoint}: Lamps Unit Empty G p o T:= ⟨(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=>  (fun i=> Empty.elim i)⟩ -- V T bind
local notation "τφ"=> R.family.path.levels.clock.op i n
local notation "hΞ"=> (P').p.supportExponent
local notation "β!"=> (P).beta
include h v l K₀
private lemma inside (r:i < N) : Topline P' (quoteR R (Ψ (i+1)).beta i):=by
   obtain ⟨U,hU,⟨WC⟩⟩:= (v.2 i l r).earns; have hm' :(1:ℕ)≤ I:= by have hm:= (S).clock.adm i; omega
   obtain ⟨Wq,y,bω,hT⟩:= h.frost.license _ _ (step_paid S i) 1 I hm' le_rfl hm'; let P₁:=hT (Φ i) (R.alloy.B.valid.pays i); obtain ⟨E,he⟩:= invited R h D Q π Γ Ψ v K₀ l r I U P₁
   have hp:=(later R π Γ Ψ v (Nat.le_succ_of_le l) r).truep; have h':= hp.valid.labels;
   let v0:PUnit.{1}→ Site (c (i+1) n):=fun _=>0
   let X':= rentValid h'.forced h'.boundK; let Λ:Gallery Unit Empty v0 P Kes:= ⟨empty,Hard.rent X'⟩
   have hb₀ := (Hard.leasing (w:=1) (α:=Unit) («R»:=Kes) (o:=v0) X'); have hγ : (A).B.a.clock.forcedAllowance (i+1) ≤ 1:=by unfold RG.Calendar.forcedAllowance RG.Calendar.monitor; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
   have hp' : Λ.Pays 1 (P).p.supportExponent 1 1:= ⟨⟨Empty.elim,(fun e=> e.elim),(fun e=> e.elim),fun x=> budget_finite (fun e=>e.elim) (by rw [Finset.univ_eq_empty,Finset.sum_empty]; exact zero_le_one)⟩,Hard.mono _ hb₀ hγ⟩
   obtain ⟨w'⟩:= Travel.sealed Λ 1 hp'; have hx:= spare R π Γ Ψ v (Nat.le_succ_of_le l) r
   have hn(i:PUnit.{1}):0<(1:PUnit.{1}→ℝ) i:=zero_lt_one
   have ht:= (Travel.docket U WC E Λ 1 w' hn hx dummy (by norm_num) () (Classical.choice (Tree.select (τφ).ratio ((τφ).patch.odd_side)))).2.1
   have hL:= Hard.transfer _ _ () ht hn; unfold Topline; rw [show (Ψ i).p.B=(X).B from congr_arg BudgetPoint.B (later R π Γ Ψ v l r.le).truep.point]; exact ⟨WC.intermediate,_,⟨WC.second⟩, hL⟩
local notation "y!"=> Willow.haloSlack (Ψ i).p.B
include hP
variable {u:ℕ}(hu : u≤ R.family.path.levels.clock.J i)(hb:i≤N)
local notation "Gx"=> Blush.glyph xd
local notation "D'"=> Gx*(xd)^(-(u:ℝ))
local notation "Obs"=>Hard.Install (P').activities (P').p
-- buy startup room. For TOP itself can use reserves at terminal
include hu hb
lemma runway : ∃ f≤ D', Topline P' f:= by
    rcases eq_or_lt_of_le hb with hb|hb; · subst i; refine ⟨_, ?_, hP⟩; rw [(AllOrder.Quay.e_all («a»:=R.family.path.levels) («n»:=N) rfl (zero_lt_one.trans ((S).fits.delayed N))).2]; exact ((h.passport _ _ (step_paid S N) _ (R.alloy.B.valid.pays N)).portions 0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) u hu).enough
    refine ⟨_,?_,inside R h D Q π Γ Ψ v K₀ l hb⟩; have he:= force_bill R h π Γ Ψ v l hb hu; have hi: xd≤ γ:=(by rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)); have hp:=zero_lt_one.trans ((S).fits.delayed i); apply he.trans ((mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hp hi (neg_nonpos.mpr (Nat.cast_nonneg _))) (Graces.glyphBound (S) i).1.le).trans_eq ?_); rw [mul_comm]; rfl
-- period/regime.POSTfolio shape deposit.Screen
open Affinity Screen Spes.Market
variable {o' k' K d r s':ℕ}
variable (hℓ: o' ≤ R.family.path.levels.clock.J i)(hK:K ≤ R.family.path.levels.clock.J i)(hd:d≤ R.family.path.levels.clock.J i)(hr:r≤ R.family.path.levels.clock.J i) (hK':k'≤ R.family.path.levels.clock.J i)
variable {V I':Type}[Fintype V][DecidableEq V]{J:Marker.Census V}[Fintype I']
variable {w:V→ℝ}{Ad:V→Orbit}(E:Spes.Screen Ad I' J G (R.family.side i n)) {L': V→Support (R.family.side i n)} (D0:∀ v,Submodule ℂ (Ad v).Mood) (o:V→Site (R.family.side i n))
variable (hX:Screen.Rooted D0 L' o E w 1 d)(hF:Screen.Loft E (o'+1) r r)(hw:∀ v,0<w v)(hV:∀ i:J.Mode,i.val.card ≤ K)
-- local notation "H"=> Market.pad o' r -- collides local earlier! 
local notation "Y!"=> (S).params i
local notation "T!"=> Market.Tray G (Y!) xd o' k' K d r
local notation "Ş"=> (Ψ i).p
local notation "G!"=> Coat.gStep (Ψ i).beta
-- payer schedule demands ceilRestoreLoan `(F.gPower)` arbitrary K.
local notation "Z*"=> K * Market.pad o' r + s'
local notation "Φd"=> Market.radiant o' k' xd
local notation "p!"=> Market.fundL o' r xd
local notation "q!"=> Display.Lens.portion Ad
local notation "v0"=> fun i=> (Φd)*w i -- notation i shadow collision? macro captures i.
local notation "WX"=> Affinity.Full (E:=fun v=>(Ad v).Mood)
-- Reservoir.L.Unlock at Screen time with exact unmasked insertion.L.Region.Geometry.
omit hu
local notation "D₀"=> Gx*(xd)^(-(s':ℝ))
include hb hX hF hV hℓ hK hd hr hK' hw
-- explicit Ω δ Rooted. needs enough since grade price > comparison scale
lemma stars (htag: K* Market.pad o' r+s' ≤ R.family.path.levels.clock.J i): ∃ x:Gallery WX I' o P' J, Adult L' D0 x ∧ (∀ t U, x.density t U=(↑((P').eval U):ℂ) • Poly.pass (E.log (G!) t U)) ∧ x.E= E.render Ş o hX G! ∧ (Affinity.readH x (Affinity.readBack (Display.Lens.portion Ad))).Pays v0 ((Ψ i).p.supportExponent) 1 D₀:= by
   have hx:=zero_lt_one.trans ((S).fits.delayed i); let β':= (Ψ i).beta; have hz:=(later R π Γ Ψ v l hb); have hR : Next.Scheduling.inBand xd (Ψ i).beta := hz.beta.symm ▸ trial_in ((R.T.sticks N n|>.prices _ (Nat.zero_le _) hb).2); have hβ:0<β':=((by positivity) : 0<xd/4).trans_le hR.1; have hN: Burn.Near xd β':= hR
   have hh:T! (Z*):= by
      change Market.Tray _ _ _ _ _ _ _ _ _; rw [PriceCompiler.params_eq R.alloy.B.valid i]; exact (h.passport _ _ (step_paid S i) _ (R.alloy.B.valid.pays i)).portions o' hℓ k' hK' K hK d hd r hr _ htag
   have he:Market.tuning Y! Ş xd:= by rw [hz.truep.point]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
   let ϕ:= Φd; have hs :1≤p!:= one_le_pow₀ hh.sized.le
   have hϕ:0< Φd:= Real.rpow_pos_of_pos hx _; have hk:0< ϕ/(p!):= div_pos hϕ (zero_lt_one.trans_le hs)
   let φ':= v0; have hv(x:V):0<φ' x:=mul_pos hϕ (hw x);
   obtain ⟨f,hZ,I'c⟩:= runway R h D Q π Γ Ψ v K₀ l hP htag hb; obtain ⟨A',e,⟨Q'⟩,ht⟩:= I'c.room -- Topline defeq
   let ψ₀:= Screen.full E hX (G!) Q' ht; let v₁ (i:V):= Φd/(p!)*w i; have hb':v₁ = Stoop.radius v0 (p!):= by ext i; unfold v₁ Stoop.radius; dsimp only; ring
   have hv'(x:V):0<v₁ x:= mul_pos hk (hw x); have hg₀:0<G!:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
   have ht' (i' : I') : 0<(E.mode i').val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun hh=> E.positive i' (Subtype.ext hh)); have hμ(i'):= hh.expect _ _ _ (hF.rank i') (hF.price i') (ht' i') (hV _) (hF.weight i') Ş he β' hN
   have he₀: d≤ (Ş).B:= hh.radius.trans_eq he.2.1.symm
   have hw0 := Willow.spare_pos (Ψ i).p.B
   let f':= Screen.furnished E hX (G!) Q' ht
   have proofBudget_at_stage:(E.shift Ş o hX G!).Budget v₁ (Ş).B (hΞ+1) (Willow.haloSlack (Ş).B):=by
       exact mul_one (Willow.haloSlack (Ψ i).p.B) ▸ (E.shifted Ş o hX (G!) hw he₀ hk hg₀ hw0.le (fun j=> (by rw [he.2.1,he.2.2.2.2]; exact (hμ j).2)))
   have hQ₀: (f').E.Paid v0 (Ş).B hΞ 1:= by
       refine (one_mul (1:ℝ)) ▸ (E.litPays Ş o hX (G!) hw he₀ hϕ hg₀ (show (0:ℝ)≤1 from zero_le_one) ?_); intro u; rw [he.2.2.2.2]; exact (hμ u).1
   let hF0:= E.money hX (G!) Q' ht hv' proofBudget_at_stage hs hV hQ₀ hb'; refine ⟨ ψ₀,E.rainforest hX (G!) Q' ht, fun t U=> ?_, E.looksLike hX (G!) Q' ht, enlarged v0 hF0 le_rfl (le_trans (mul_le_mul_of_nonneg_left hZ (by have h:= hs; positivity : 0 ≤ p! ^ K)) (le_of_eq ?_)) ⟩
   · have HH: f'.Pays v0 hΞ 1 (p!^K*f):=by rw [← (ampl Ad).reverts f']; exact hF0
     exact E.offered hX (G!) Q' ht hv' proofBudget_at_stage hv HH t U
   unfold Market.fundL; rw [← pow_mul, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_neg hx.le,Real.rpow_natCast,pow_add,mul_comm K (Market.pad o' r)]; field_simp
end Uplink
end YM.QuadraticLocal.Advent
