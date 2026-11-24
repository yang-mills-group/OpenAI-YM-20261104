import YM.LocalLTE.Concert.Aurora
import YM.LocalLTE.Concert.Poster

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
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J

namespace Career
open Progress.DirectedRecipe
open YM.LocalLTE.Port YM.LocalLTE YM.LocalLTE.FrameBox YM.LocalLTE.Port.LoopBank
open YM.Marker YM.Overlay
local notation "Y"=> betaF G x₀ L
local notation "f"=> A.B.a.S.side (m+1) n
set_option quotPrecheck false
variable {r t T u b kB Ra:ℕ} {μ ζ J':ℝ} (x:ℝ) (hp':Posters b t kB J' μ ζ H.κ Ra A.delay)
variable (hc:ℝ) (hμ:0≤μ)
variable {V α : Type}[DecidableEq V][Fintype V][Nonempty V][Fintype α](L₀: Marker.Census V)
variable (X':LoopBank G (A.B.a.S.side (m+1) n) L₀ α )
variable (hs:Fintype.card V≤ kB)(hq:Fintype.card α ≤ t)
variable (FL:(i:α)→ Grove (X'.scene i))
variable (hy:X'.Legit L₀ b J' ((betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))^μ))
variable (hw0:∀ i:V,(neat (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) μ)* ‖X'.units i‖ ≤ hc)
local notation "bw"=> (fun _:V=> neat Y μ)
local notation "PT"=> F.holds.latch x
local notation "V!"=> Q (F.holds.latch x)
local notation "W'"=> Mallow.spread A.B.a N p n (m+1)
local notation "S'"=> (X'.baked V! L₀ b)
local notation "Cℓ"=> (Port.posta V! L₀ (S')) -- shadows? C₀ earlier def
local notation "M'"=> (X'.model L₀ b Ra H.κ FL)
local notation "D'"=> (Port.crystal V! (S') M')
local notation "E'"=> (Port.thaw V! (S') M')
local notation "κ"=> H.κ
local notation "U'"=> ((L).val*radiusB x₀)
-- aux costs per center.
local notation "P'"=> (V!).p
local notation "v'"=> (X.p.profile J)
local notation "YW"=> (Y^μ)
local notation "Δ"=> (Y^(-ζ))
local notation "φ0"=> slotPay G J' b (V!).p.order (V!).p.power
local notation "U₀"=> LoopBank.costAP t (neat Y μ) P' b
local notation "π"=> (U₀ φ0 (Y^μ))
local notation "γ₁"=> (U₀ (φ0+Δ) (Y^μ))
local notation "e"=> (U₀ Δ (Y^μ))
local notation "δ"=> (A.B.a.clock.forcedAllowance (m+1))
local notation "ν"=> Real.sqrt (δ)
variable (η:ℕ)(hη:Ra ≤ η+1)
variable (Ra b t μ ζ J')
structure Enthral :Prop where -- binder notation earlier uses section vars: notation captures variables b old? test compiler.
    legal : (Cℓ).Active∧(D').Active∧(E').Active
    bulk: (Cℓ).Radial (bw) hc (π) Δ ν
    past: (D').Radial (bw) hc (γ₁) Δ ν
    trace: (E').Radial (bw) 0 e Δ ν
    spirit: Port.Shine L₀ (D') η U' H.κ
    pilot : Fan.Tabs V! L₀ (Cℓ) D' E'
    energy: Port.capacity (V!).p V (γ₁) e ν Δ (Y^ζ) U' ≤ Y^(-(1:ℝ))
    authentic U: (Cℓ).density U = ((V!).eval U:ℂ) • Marker.Poly.pass (Extra.Trajectories.Layers.logPart S' U)
variable {Ra b t μ ζ J'}
-- actual all registered probes. units priced w.B.Car
variable (hg: HasSlots (Q (F.holds.latch x)).p (Q (F.holds.latch x)).activities)
include hp' hs hq hy hw0 hμ hg hη
lemma sugary : Enthral H F t b Ra μ ζ J' x hc L₀ X' FL η:=by
    let X₀:= v'; have he:= step_paid A.B.a m
    obtain ⟨hw,ht,hS,hK⟩:=hp'.pays J I he x₀ (A.B.valid.pays m) -- U x
    have hp := (F.turns _ (F.holds.latch x).property).1
    let i:= m+1; let R:= V!; let T':= P'; have hG:T'.order=(v').order := (congr_arg BudgetPoint.order hp.point).trans (congr_arg Stage.order (params_eq A.B.valid i)) -- adjust
    have hG':T'.power=X₀.power:= (congr_arg BudgetPoint.power hp.point).trans (congr_arg Stage.power (params_eq A.B.valid i)); have hV:T'.supportExponent=X₀.supportExponent:=(congr_arg BudgetPoint.supportExponent hp.point).trans (congr_arg Stage.supportExponent (params_eq A.B.valid i))
    let β:= betaF G x₀ L
    have h₁ : A.B.a.clock.hatBeta i=β:= beta_eq A.B.valid m
    have h₂:ν=Urns.divisor β:= by change Real.sqrt (Real.exp (-((A.B.a.clock.monitor i)^(1/5:ℝ))))=_; unfold Calendar.monitor; rw [h₁]; rfl
    have hQ: T'.threshold=temp β:= by unfold T'; rw [hp.point,← h₁]; rfl
    have hj := A.B.a.fits.sizeT (m+1) n
    have hF: radiusB β+1 ≤ (A.B.a.S.side (m+1) n).val:=by rw [← h₁]; unfold i; apply le_trans _ hj; change radiusB _ +1 ≤100*(radiusB _ +1); omega
    obtain ⟨hu,hW,hZ⟩:= hK V hs (R).p hG hG' hV hQ -- syntax
    have h(r): R.p.supBounds (X'.scene r) (X'.wires L₀ b r) (X'.realSignal L₀ r-X'.modelRain L₀ b Ra H.κ FL r) (β^(-ζ)):=by
        have hh: 4*(b+1) ≤ radiusB β:=ht; exact hZ f (by omega) (by omega) _ _ (X'.tone r) (hy.traced r) (hy.closes r) (hy.conjugacy r) (hy.traces r) (FL r)
    let τ:=(β^μ); let ξ:=β^(-ζ); have hβ:0<β:=zero_lt_one.trans_le hw
    have ht': (Urns.divisor β)^2=(δ):=by rw [←h₂, Real.sq_sqrt (by exact Real.exp_nonneg _)]
    let μ':= neat β μ; have hμ':0<μ':=Real.rpow_pos_of_pos hβ _
    have hx:neat β μ ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos hw (by linarith only [hμ]); let u:= (φ0); have ha:0≤u:= Mallow.budgetR b J' (X:=R) (hy.possible.1) -- order check
    have hP': u=slotPay G J' b X₀.order X₀.power:=by change slotPay G J' b T'.order T'.power=_; rw [hG,hG']
    have hv:R.activities.Valid R.p _ (δ):= hp.valid.labels
    have hD:0< ν:= (h₂.symm ▸ Urns.nonzero β)
    have hc':0≤ξ:= Real.rpow_nonneg hβ.le _; have hY:gross t b R.p (δ) (τ*u)≤ ξ*(ν):=by rw [hP',h₂,← ht']; exact hW
    obtain ⟨h,hM',hC,hK,hP,hE⟩:= X'.crystals R L₀ b Ra H.κ FL H.paid.choose_spec hy h (bw) (fun _=> hμ') (fun _=> (le_refl μ')) hx hμ'.le t hq (Real.exp_nonneg _) ha hg hv hc' ν ξ hc hD hc' hw0 hY -- order.T
    refine ⟨⟨h,hM',hC⟩,hK,hP,hE, X'.illuminant R L₀ b Ra H.κ FL η U' hη hS, Port.cleansed R S' M',?_ , Port.nocturne R L₀ _ hg (X'.raysP R L₀ b hy) hv⟩ -- edit namespace
    change Port.capacity R.p V (U₀ (u+ξ) τ) _ _ _ _ _≤ _; rw [hP',h₂]; exact hu
end Career
end YM.PhysicalNext.Repeat.Mallow
