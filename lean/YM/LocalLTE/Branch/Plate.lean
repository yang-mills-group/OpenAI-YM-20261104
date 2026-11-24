import YM.LocalLTE.Branch.Shape
/-! Strict capacity at Actual Returns on station. Forced divisor. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Urns
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- compact socket avoids Pie SAM goals; not obligation records encoding analytic estimates.
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {E:ℕ→ℕ→Exchange} {bt:Baton G} {u t : Return.Wages} {Bn:ℕ→ℕ→Booth} {J:ℕ→ℕ→JointLoad.Clockwork.Menu} {P:ℕ→ℕ→JointLoad.Heir.Record} {L : ℕ→ℕ→JointLoad.Folio.Aux} {c c₁ c₂:ℝ} {q:UVNext.CouplingReset.ResetPrices} {η:ℕ→ℝ} {r:ℕ→ℕ→ℕ} {T:Programs X.p} {Y: ℕ→ℕ→Cafe}
    (h : Roof.Sheltered (C:=T) (B:=Y) A bt u t r Bn J P L R S (1/16) (1/16) (1/8) E q η)
    {N m n : ℕ} {Q: UVNext.CouplingReset.In A.B.a m n} {a:ℝ} (hm: m<N)
open YM.LocalLTE.Inset ClockB
variable {l κ q' η' : ℝ}{p' ℓ:ℕ}(W:Wind p' η') (hk : Reliable G κ q') {d:ℕ→ℕ→ℝ}
    (hV:Roof.WorksIn R A.post A.delay S) (hX:Spoke D R W A.post κ d A.delay)
    (ht:AsDivisors A.B.a.S)
    (hC: (C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O)
    (M:Maps (A:=A) (C:=C) W m N)
    {V':RG.Rep G (A.B.a.S.side (m+1) n)} (hl:Lives A.B.bake N (m+1) n V') (hb:V'.beta∈band A.B.a (m+1))
    (U:Guide A.B R N m n V') (hU:Opera.Price A.B R N m n V' U)
    (X':Expose (A:=A) (R:=R) W V'.beta N m)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "b" => Trio.resize W.ℓ (Rain.lint C A m)
local notation "z" => Trio.base b (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "T'" => A.B.a.clock.op m n
local notation "e₁" => Time.forecastE A.B.a m
local notation "k₀" => Time.forecastK A.B.a m S V'.beta
local notation "s₀" => ClockB.lanternPay G (D.L Jp) (X.p.profile Ip) W.q x₀
local notation "γ" => A.B.kin.alpha N m
local notation "T₁" => (A.B.a.params m)
local notation "T₀" => (X.p.profile Ip)
local notation "Ce" => (((1/16+2*(1/16:ℝ)))*Time.forecastE A.B.a m)
local notation "ζ"=>betaF G x₀ (D.L Jp)
local notation "Q'"=>fronts (m:=m) (C:=C) (A:=A) W
local notation "PU"=>Meadow.intern U
local notation "χ"=>Chi.canonical
local notation "f'"=> M.reader W κ (d Jp Ip) (gStep V'.beta)
set_option quotPrecheck false
-- addresses from PET template. high kinetic independently determined too. Z depends M.Path, order, threshold, level m,N,n.
open Magnet
local notation "K₀" => A.B.kin.path N m
local notation "a₀" => (A.B.a.params m)

local notation "q₀"=> quota W A m
local notation "δT"=> VerifiedReset.Averaging.delta
variable (hG:G.Simple) {k:ℕ}{G₀:Forest (A.B.a.clock.op m n).ratio}{k':Return.Bookings A.B m n p} (hx:Firings W M U X' S κ (d (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) k Y G₀ k')
local notation "R'" => (stock W U)
local notation "s'" => (reads W U X' k)
local notation "d₀" => d Jp Ip
local notation "f₀" => corePlan W M κ (d Jp Ip) (gStep V'.beta) n
local notation "H"=> earnt U
local notation "e₀" => smog W M U X' (d Jp Ip) κ k
local notation "P'" => (A.B.a.S.side m n)
local notation "D'" => (baked W U X' k)
local notation "F'" => (printed W M κ d₀ (gStep V'.beta) n)
variable {ω' : ℝ} (hj: Balance D A.post A.delay p' W.e ω')
-- Gains derivative rates as per B.order. Eg power target; ratios.
local notation "g₀" => gStep V'.beta
local notation "cost'"=> ((gStep V'.beta) ^ (p'+1-ω':ℝ))
local notation "σ'"=> divisor x₀
include hj hb
lemma center_cost : (Time.base G (A.B.a.params m)+1) * quota W A m ≤ cost' ∧ Return.forcing A.B m ≤ divisor x₀ * cost':= by
  have hh : Set.Icc ((ζ)/2) (2*(ζ))=band A.B.a (m+1):= by unfold RG.Shoot.band; rw [PriceCompiler.beta_eq A.B.valid]
  have hs:= hj _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) V'.beta (hh.symm ▸ hb|>.1) (show _ from (show _∈ Set.Icc _ _ from hh.symm ▸ hb)|>.2) -- typing
  have hr:(A.B.a.clock.monitor (m+1))=Delay.fineMonitor G (D.L Jp) x₀:=by unfold Calendar.monitor Delay.fineMonitor Vac.Numbers.P; rw [PriceCompiler.beta_eq A.B.valid]
  unfold quota Return.forcing; rw [hr, PriceCompiler.beta_eq A.B.valid,PriceCompiler.params_eq A.B.valid m]; exact ⟨hs.1,(div_le_iff₀ (nonzero x₀)|>.mp hs.2).trans_eq (mul_comm ..)⟩
omit hj
include hG hm h hl hx
omit hx in
lemma charts_p (f:ℕ→ Config G (P')→ℝ) (α a':ℝ) (hp: Meadow.Budget B ((R').reg) f a') :
    let V₀:= Magnet.traceE G (P') (advanced (stock W U) K₀ (T₁).clip B f α)
    V₀.RegularFamily B ∧ V₀.EBound (B) (regularNeed G (B) (T₁).clip (T₁).width (T₁).paths α a'):=by
  have hh:= h.conducts.machine.passes hm («Q»:=fun _=>V') (l:=Set.univ) (fun _ _=>⟨hl,hb⟩)|>.1; apply Magnet.receives hG (A.B.support.cap _ _ hm.le) hh.decent hh.width hp (Return.enough_room A.B ..) α
-- post-price actual
include hj
lemma prices :
    let V₀:= traceE G P' (postAncestor W U)
    let V₁:= traceE G P' (postFog W M U X' κ d₀ k)
    V₀.RegularFamily (B) ∧ V₁.RegularFamily (B) ∧ V₀.EBound B (Time.base G (A.B.a.params m) * Ce)∧
     V₁.EBound B (cost')∧ (D').activities.KBound (B) (Real.sqrt (A.B.a.clock.forcedAllowance m) * cost')∧
     (B).threshold^2* |heirΔ W U| ≤ Ce ∧ (B).threshold^2 * |mistΔ W M U X' κ d₀ k| ≤ cost':= by
  intro V₀ V₁; let Z':= postAncestor W U; let R'':= (R'); let P:=(B)
  obtain ⟨hh,hF⟩:= charts_p h hm W hl hb U hG _ 0 _ hx.ancestry -- hx removed later
  obtain ⟨hE,hM⟩:= charts_p h hm W hl hb U hG _ 0 _ hx.pressure
  have hp (i:ℝ): regularNeed G (B) (T₁).clip (T₁).width (T₁).paths 0 i = Time.base G T₁ * i:= by rw [Time.table G (T₁) (show Time.Same (T₁) (B) from ⟨rfl,rfl,rfl⟩)]; simp
  rw [hp] at hF hM; obtain ⟨h₁,h₂⟩:= Urns.center_cost W hb hj
  have hu: 0 ≤ quota W A m := Real.rpow_nonneg (zero_le_one.trans (le_of_lt (A.B.a.fits.delayed _))) _
  have hv:= hx.offer; have hk: (D').activities.KBound (B) (Return.forcing A.B m):= hx.offer.bundle.point ▸ hx.offer.forced
  refine ⟨hh,hE,hF, Time.E_rises hM ((mul_le_mul_of_nonneg_right ?_ hu).trans h₁), Time.K_rises hk h₂, VerifiedReset.Averaging.delta_bound hG (Magnet.promoted hx.ancestry), (VerifiedReset.Averaging.delta_bound hG (Magnet.promoted (X:=R'') hx.pressure)).trans ((le_mul_of_one_le_left hu ?_).trans h₁)⟩
  · linarith
  have he:= Time.base_nonneg G (A.B.a.params m)|>.1; linarith
-- cancel v absolute EXACT by actual denominator; not fanout
omit hG hm h hl hj hb
lemma settle (i: Config G (P')) :
    let Yd:=(baked W U X' k)
    let Y₀:=(A.B.a.clock.op m n).push V'.beta V'.eval
    Y₀ 1=Real.exp (Yd.v*Fintype.card (Site P')) ∧ 0 < Y₀ 1∧ Y₀ i / Y₀ 1=({ Yd with v:=0} : RG.Rep G _).eval i:= by
  intro Yd Y₀
  have hh:Y₀=Yd.eval:=hx.offer.ident.symm
  let M₀: UVNext.CouplingReset.Template G (P'):= ⟨Yd.path,Yd.clip,Yd.p,fun _ _ => Yd.activities⟩
  have he : M₀.trial (fun _=>Yd.beta) 0 0 Yd.v= Yd:= by simp [UVNext.CouplingReset.Template.trial,M₀]
  rw [hh]; have hp: Yd.eval 1=Real.exp (Yd.v*Fintype.card (Site P')):= by rw [← congr_fun (congr_arg RG.Rep.eval he) 1]; exact M₀.trial_one _ hx.offer.bundle.valid.labels.regular.at_flat
  rw [hp]; refine ⟨rfl,Real.exp_pos _,(div_eq_iff (Real.exp_pos _|>.ne')).mpr ?_⟩
  unfold RG.Rep.eval RG.Rep.exponent; rw [mul_right_comm (Real.exp _) (Yd.activities.gas Yd.p i), ← Real.exp_add]; dsimp only; ring_nf
end YM.PhysicalNext.Repeat.Urns
