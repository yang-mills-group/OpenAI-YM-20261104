import YM.LocalLTE.Crafts.Bands
import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Estate.Lien
import YM.LocalLTE.Pool.Dawn
import YM.LocalLTE.Bonnet.Canopy
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
variable {p:ℕ}(W:Trail H p)(M:Preview H)(v:Bolt A)(hv:Made H W M v)
open Progress.DirectedRecipe Averaging LocalLTE.FrameBox Price
variable (k':ℕ)
local notation "t'"=> Mallow.spread A.B.a N p n (m+1)
local notation "X'"=> (F.barn H W k' t')
set_option quotPrecheck false
local notation "V!" x=> F.Voy H W k' t' k x
local notation "α"=> (A.B.a.clock.allowance m)
local notation "q"=> (A.B.a.clock.forcedAllowance m)
variable (r:ℕ) (h:Mallow.Outlook r p A.delay) (hm:m<N) (J':Adorn H W) (hs:Film H W M F k k' hm)
open Extra.Histories
variable (R':Rep G (A.B.a.S.side (m+1) n))(V:Rep G (A.B.a.S.side m n))(x:ℝ)
-- Forecast minus increments.Plan.Model.Buses USE with Film.H.Algebra. explicit connectivity.H covariance retained. Choose for real at normalized conditional vacuum at identity. Full atlas early.Price Evolved.W.N..
local notation "g"=> gStep R'.beta
local notation "e₀"=> ((gStep R'.beta)^ (↑r+1:ℝ))
local notation "Z"=> F.proposals H W k' R'
local notation "π"=> A.B.a.clock.op m n
-- Claims: full histories from all-prior License.Alpha kinetic plan entirely same M. β update cost after.Hessian. no comparison of M stationary to continuum. Entire λ_t.Mark later
structure Peg (k:ℕ) : Prop where
    film : Film H W M F k k' hm
    entry : x∈s
    inlet : Q x=R'
    outlet : F.Voy H W k' (Mallow.spread A.B.a N p n (m+1)) k x=V
    actual : A.B.Move N m n V R'
    accuracy : Accurate A.B R.post N m n V R'
    lives : Grain H W N m n V
    photo (i:ℕ): Z i= if Price.grade (A₀) p i ≤p then V.activities.E i else 0
    receipt : (Mallow.charged V.activities (F.proposals H W k' R')).Valid B α (Real.sqrt q*e₀)
    pride : (Mallow.charged V.activities (V.activities.E-Z)).Valid B e₀ (Real.sqrt q*e₀)
    drift : |V.beta - (R'.beta+γ+F.chipK H W k' R' p)|≤e₀
    charge : (π).push R'.beta R'.eval 1=Real.exp (V.v*Fintype.card (Site A₀))
    norm (U:Config G (A₀)): (π).push R'.beta R'.eval U / ((π).push R'.beta R'.eval 1) = ({V with v:=0}:Rep G (A₀)).eval U
    -- additional witness λ forecast sources.Norm local.
variable (hb:x∈s)(hG:G.Simple)
include hb hm J' h hG hs
lemma pegged : Peg H F W M k' r hm (Q x) (F.Voy H W k' t' k x) x k:=by
    let U:=V! x; let E:= Q x; let f:= t'; let y:= x₀; let b:= E.beta; let t:= betaF G x₀ (D.L J)
    obtain ⟨hm',hq,hr,hL⟩:= F.accepted H W hm k' f J' hs.motion hs.cards hG x hb (hs.spring _ hb) (Opera.forum A.B R.shape)
    have hp:= hm'.bundle
    have hz := F.turns x hb; have hv: E.beta∈Set.Icc (t/2) (2*t):=by obtain ⟨hv,he⟩:= hz; unfold RG.Shoot.band at he; rw [beta_eq A.B.valid] at he; exact he -- edit
    let e:= gStep b^(↑r+1:ℝ); obtain ⟨hE,hV,hΔ⟩:= h _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) E.beta (le_trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)) (by norm_num)) hv.1) hv.2
    have hh : q≤Real.sqrt q*e:=by
       have ht : Real.sqrt q ≤e:=hV
       have hq : 0 ≤ q:= Real.exp_nonneg _
       rw [← Real.mul_self_sqrt hq]; conv_rhs => rw [Real.mul_self_sqrt hq]
       exact mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
    have hVV: U.activities.Valid U.p α (Real.sqrt q*e):= { hp.valid.labels with boundK:=Time.K_rises hp.valid.labels.boundK hh } -- U valid
    obtain ⟨hs₀,hU⟩:= Mallow.components U (Price.grade (A₀) p) _ _ hL (F.uplink H W k' _ hb) (A.B.a.fits.delayed m|>.le) hVV (fun i p'=> F.coil H W k' x i p' (hVV.moves ..))
    let S:= π; have hv₀ : S.push E.beta E.eval = U.eval:= hm'.ident.symm
    have hJ : U.eval 1=Real.exp (U.v*Fintype.card (Site A₀)):= by
       let V₀: Template G (A₀):= ⟨U.path,U.clip,U.p,fun _ _=>U.activities⟩
       have he:V₀.trial (fun _=>U.beta) 0 0 U.v=U:=by simp [Template.trial,V₀]
       rw [← congr_fun (congr_arg Rep.eval he) 1]; exact V₀.trial_one _ hVV.regular.at_flat
    refine ⟨hs,hb,rfl,rfl,hm',hq,(by unfold Grain spread; rw [if_neg hm.ne]; exact hL),F.uplink H W k' _ hb,hs₀,{hU with boundE:= Time.E_rises hU.boundE hE},?_ , (congr_fun hv₀ 1).trans hJ,fun i=>?_⟩
    · let f':= F.index H W k' f k x; let t₀:= F.school H W k' f; let d:= F.chipK H W k' E p; let α':= Averaging.delta (t₀.read f')
      have hk := F.atEarn H W hm k' f hs.motion hs.cards _ hb; let p':=(B); obtain ⟨ν,h',hc⟩:= hk.cheap; have hu: p'.threshold^2* |α'-d| ≤ 2*W.hop H m*t^(Pastel.chip (p+1)):=by
          unfold d Career.chipK; rw [F.sav H W k' p x hb]; exact (Price.levy hG t₀ f' (show Meadow.Budget B t₀.reg f'.logRead (W.hop H m*t^(Pastel.chip 0)) from ⟨ν,hc,fun i=> ⟨hk.smooth i,h' i⟩⟩) (F.primordial H W hm k' f J' hs.motion hs.cards x hb p le_rfl (hs.spring _ hb))).1 -- infer
      have hρ : U.beta=E.beta+γ+α':=rfl
      change |U.beta-(E.beta+γ+d)|≤_; rw [hρ,add_sub_add_left_eq_sub]; have hP:= W.income J I
      have hx':0 ≤ t^(Pastel.chip (p+1)):= Real.rpow_nonneg ((by unfold t; exact zero_le_one.trans (A.B.a.fits.delayed m|>.le.trans (le_add_of_nonneg_right (Work.E04.shift_nonneg ..))))) _
      exact ((le_div_iff₀ (sq_pos_of_pos p'.threshold_pos)).2 ((mul_comm _ _).trans_le (hu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP.2 zero_le_two) hx')))).trans hΔ
    change S.push E.beta E.eval i / S.push E.beta E.eval 1 = ({ U with v:=0} : Rep G _).eval i
    rw [hv₀,hJ]; apply (div_eq_iff (Real.exp_pos _|>.ne')).mpr; unfold RG.Rep.eval RG.Rep.exponent; rw [mul_right_comm (Real.exp _) (U.activities.gas U.p i), ← Real.exp_add]; dsimp only; ring_nf
end YM.PhysicalNext.Repeat.Mallow
