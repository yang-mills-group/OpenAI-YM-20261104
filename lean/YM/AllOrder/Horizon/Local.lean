import YM.AllOrder.Horizon.Order
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-! # moving polymer cutoff and warm licenses on the ORIGINAL level of the construction -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} (A : Alloy X D) (F: Factor A) {c f : Side} {m n N : ℕ}
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
set_option quotPrecheck false
local notation "W" => (A.B.a.params m).clip
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)

variable {η : ℕ→ℕ→ℝ} (H : Lodge D F.shape η A.delay)
include H
lemma lot : Summit D R η I J x₀:= H.terms J _ (A.B.valid.pays m) I (step_paid a m)
-- ">2 Tro" from Ledger.post.
lemma room_full : 2 * Trio.base Y B < (A.B.a.S.side m n).val := by
  let h:=A.delay.growth J; let s':=(A.B.a.clock.coverSize (m+1)); let e:=Y; have hh:=H.sizes _ _ (step_paid A.B.a m)
  have he: 1 ≤ B:= (V).B_pos
  have hm:= Trio.roof Y B he; have hv:0< Trio.maxFixed Y:= by unfold Trio.maxFixed Trio.base Trio.tent; omega
  apply lt_of_lt_of_le _ (A.B.valid.volume m n); change _ < A.delay.shells J * (1+B+s')^h; apply lt_of_le_of_lt hm; refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ hh); apply Nat.mul_lt_mul_of_pos_left _ hv
  exact lt_of_lt_of_le (b:=1+B+s') (by omega) (le_self_pow₀ (by omega) (show h≠0 from Nat.ne_of_gt (show 0<h from H.cost_growth J)))

omit H
include F
lemma decent (hm : m<N): WilsonStartup.Decent W V := by
  let Pp:= A.B.a.budget (m+1); let X:= A.B.a.S.side (m+1) 0; let C:(X).val=X.val:= rfl
  let Q (x:ℝ):= Pane.virgin (orchestra A N (f:=X) (m:=m) (A.B.a.S.oneStep m 0).exact_size) Pp x
  have h:= F.machine.passes (Q:=Q) hm (l:=∅) (p:=0) (fun _ h=> False.elim h)
  exact h.1.decent

section read
variable (π:f.val=c.val*(A.B.a.S.block m).val) {U:RG.Rep G f} (hm:m<N)
local notation "Σ₀" => orchestra A N π
local notation "V₁" => (A.B.a.budget (m+1))
include H hm
lemma appointed (Z:Chartlet R A N m π U) :
    ∃ (C' d' v t A' b r B' q i : ℝ) (k:ℕ) (N':Captain Z (E).order C' d' v t A' b r B' q k O), KeyStone Ω u Z (E).order (E).power Chi.canonical N' (z ^ (seam_hat I-1)) i:= (lot A F H).sails c f _ Σ₀ Z.laws.data.funds (Pane.ovation A N π hm F.pledging.conducts.full) U Z
omit H in
lemma weight (Z':Chartlet R A N m π U) (hv : SeekR R A N m π Z') (P':Forest (Pane.panel A m π).ratio) : let X':= Match.staple (H:=Z') («J»:=Z') rfl rfl rfl; let b':= plusone Z' X' O γ; let G₀ := posting V Z'; Collection.Local G₀ V b'
    (turnFee V * (z^(Ω).wanting + z ^ (-(7/16):ℝ))) (Cash.armK (P) L (F.shape.μ J I) x₀ 0 (Ω).degrees) ∧ ∀ V',(Pane.panel A m π).push U.beta U.eval V'=earlyValue G₀ (Σ₀).down (Σ₀).low (V) b' U.beta (weighty Z' O P') γ V' :=
    lays R A π _ F.inn.chip hm F.pledging.jewels F.pledging.conducts.full (F.pledging.agenda _ _ (step_paid A.B.a m)|>.1) (decent A F hm) hv P'
set_option maxHeartbeats 200000 in
lemma skirt (Z': Chartlet R A N m π U) (h':SeekR R A N m π Z') (he : ∀ i,U.activities.E i=0) :
    ∀ᶠ k in atTop, Meadow.Budget V ((Beam.marquee Z' V).reg) (High.leftover (strands u (steady Z' u k)) O k γ|>.logRead) (z ^ seam_hat I) := by
  let F':= Classical.choice (Tree.select (Pane.panel A m π).ratio (Pane.panel A m π).patch.odd_side)
  let P':=V; let Q:=A.B.a.params m; let X':=(Match.staple (H:=Z') («J»:=Z') rfl rfl rfl); let R':= u; let kQ:= lot A F (m:=m) H
  obtain ⟨x,y,r,s,b,t,w,l,c',o,j,hk,hK⟩:= appointed A F H π hm Z'
  have hp:= (step_paid A.B.a m)
  have hx:Q=E:= params_eq A.B.valid m; have hj : P'.order=(E).order:=congr_arg RG.Stage.order hx; have hh : P'.power=(E).power:=congr_arg RG.Stage.power hx
  have hz:0< z:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact zero_lt_one.trans (A.B.a.fits.delayed _)
  let v:= z^(seam_hat I-1); have hV := hit_trust (Height.tiredV Z' u) V O hk hK.height rfl rfl hj.le hh.le (show (V).supportExponent+3≤(Ω).earn from (congr_arg (fun q:Stage=>q.supportExponent+3) hx).trans_le (F.pledging.agenda _ _ hp|>.1))
  let T:=Σ₀; let C:= A.B.a.clock.loopCap m
  have hB : (V).threshold ≤ 2*Pressure.fiery G x₀ L:= by rw [← Z'.laws.data.funds.length_eq]; exact Z'.laws.data.room.temperatures
  have he':(V).supportExponent= (E).supportExponent:=congr_arg RG.Stage.supportExponent hx
  have hg:= suns R A F.inn.chip hm π Z'; have hL := Z'.laws.data.funds.length_eq; have hf : T.down.Bounds T.low Q.width Q.paths C:= A.B.support.cap N m hm.le
  have hs := (lot A F (m:=m) H).script 0 (Nat.zero_le _)
  have ht : |U.beta|≤2*z:= by rw [abs_of_nonneg (Z'.laws.intake.positive.le),← hL]; exact Z'.laws.intake.window.2
  have hΛ: Real.exp (-(Q.width/4)*P'.B)*Song.octaveNeed G P' T.low Q.width Q.paths C U.beta γ ≤ v:= by
    rw [show T.low=Q.clip from rfl,hx]; exact kQ.ducts P' hB hh hj he' rfl _ _ _ ht (Boulevard.coupling A _ _ hm) (coverBill ..|>.1) ((coverBill ..).2.trans (brace _ hs.1))
  have ha := cruise _ V O γ hV rfl hf (decent A F hm) hg.1 hΛ
  filter_upwards [finite_bonus _ V O γ (weight A F π hm Z' h' F').1 (fun k=> strands R' (steady Z' R' k)) (fun i hx hy => pursuit Chi.canonical he i hx hy.choose hy.choose_spec) ha (show 0<v from Real.rpow_pos_of_pos hz _)] with k he
  · obtain ⟨f,hf,hg⟩:=he; exact ⟨f,fun i=> budget_loosen (hf i) (kQ.total (P') hj hh),hg⟩
end read
end YM.AllOrder.Shop
