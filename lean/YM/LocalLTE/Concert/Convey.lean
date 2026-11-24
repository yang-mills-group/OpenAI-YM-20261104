import YM.LocalLTE.Concert.Hosts
import YM.LocalLTE.Concert.Fuse
import YM.LocalLTE.Rendezvous.White
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
variable (hg: HasSlots (Q (F.holds.latch x)).p (Q (F.holds.latch x)).activities)
variable (d0:ℕ→ℕ→ℕ) (JX:Adorn H W) {J₀:ℝ}
   (Z:ConcertZ R.target p ζ) (hk:ConcertZ.CalendarQ R.shape d0 Z H.κ A.delay)
   (hb:Merchandise R.shape W.footprint W.ψ A.delay)
   (hkz:Z.strength=fun _ _=>ζ)
variable {R₁:Rep G (A.B.a.S.side (m+1) n)} {Q₁:Rep G (A.B.a.S.side m n)} (M:Preview H)(hQ:Peg H F W M k' r hm R₁ Q₁ x k) (hcG:G.Simple)
variable (hh: Enthral H F t b Ra μ ζ J' x hc L₀ X' FL (d0 (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)))
variable (v:V)
local notation "Q'"=> F.Voy H W k' W' k x
local notation "t'"=> (d0 J I)
local notation "MX"=> (Port.Mosaic D' E' U')
open MergeProof.Menu
variable (Ra b t μ ζ J') -- notation in declarations.Int.
local notation "Y'"=> (Y^ζ)
local notation "Qo"=> (A.B.a.clock.op m n)
-- abbreviations MENUs.M.Composite. Use Ω.Adj.Role. No collision.
local notation "Ω"=> Port.Aurora H.κ D' bw (t') U' γ₁
variable (k)
variable (N' : Port.Mosaic (Port.crystal (Q (F.holds.latch x)) (X'.baked (Q (F.holds.latch x)) L₀ b) (X'.model L₀ b Ra H.κ FL)) (Port.thaw (Q (F.holds.latch x)) (X'.baked (Q (F.holds.latch x)) L₀ b) (X'.model L₀ b Ra H.κ FL)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB (A.B.a.clock.hatBeta m)) → MergeProof.Menu.Hat L₀ (Q (F.holds.latch x)))
variable (φ: Port.Mosaic (Port.crystal (Q (F.holds.latch x)) (X'.baked (Q (F.holds.latch x)) L₀ b) (X'.model L₀ b Ra H.κ FL)) (Port.thaw (Q (F.holds.latch x)) (X'.baked (Q (F.holds.latch x)) L₀ b) (X'.model L₀ b Ra H.κ FL)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB (A.B.a.clock.hatBeta m))→ Config G (A.B.a.S.side (m+1) n)→ ℝ)
local notation "LΩ"=> (Port.liners D' U')
local notation "Jr"=> F.hearth H x
local notation "oζ"=> ((Qo).ratio.parent ∘ (X'.origin))
local notation "χM"=> (fun i=>(N' i).M)
local notation "rM"=> (fun i=>sumFee (N' i) bw)
local notation "f!"=> (F.hearth H x)
local notation "E₁"=> (Port.star D' E')
local notation "cX"=> (fun i:Fan.Stars (F.hearth H x) χM=> FrameBox.cane (Fan.origin (χM) (f!) i))
local notation "ZB"=> (filmζ H F W' x χM d0 Z hk φ E₁ cX)
local notation "ϑ"=> (fun i=> MergeProof.Menu.sing (N' i) bw)
local notation "m'"=> (motto H F W k' W' x χM rM d0 Z hk φ E₁ cX L₀ ϑ oζ v k)
local notation "m0"=> Fan.exactE χM (F.hearth H x) Chi.canonical
local notation "Xζ"=> menuZ H F W k' W' x χM rM d0 Z hk E₁ L₀ ϑ oζ v k
local notation "t0"=> (Xζ m0)
local notation "p'"=> (Xζ (m0-ZB))
local notation "tι"=> Port.augment t0 (X'.units)
local notation "mi"=> Port.augment m' (X'.units)
local notation "e'"=> ((gStep R₁.beta)^(r+1:ℕ))
local notation "ν₀"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "W₂"=> (fun _:V=>(1:ℝ))
local notation "T₁"=> Y^(μ+2)
local notation "T₂"=> (Y^((μ+2)*kB))
include hk
variable (kB r R₁ Q₁) -- mark section etc 
structure Passage:Prop where -- old notation r captures earlier variable.C.
    tagIn : V! = R₁
    tagOut: Q'= Q₁
    pits: Pits H F x d0 Z L₀ Cℓ D' E' bw N' φ
    fires: OperaZ H k F W k' W' x d0 Z hk L₀ Cℓ D' E' bw v N' φ hc
    -- preserve clean and true densities AT ACTUAL U.Out.State normalization.
    wind : ∀ V:(Config G f), (Cℓ).density V= (R₁.eval V:ℂ) • Marker.Poly.pass (Extra.Trajectories.Layers.logPart (X'.baked R₁ L₀ b) V)
    charges U: (Qo).push R₁.beta (Cℓ).density U= (tι).density U
    normal U: (tι).density U=(Qo).push R₁.beta R₁.eval 1 • ((shear Q' L₀ tι).density U)
    tariff : (p').Radial (fun _=>1) 0 e' e' (Real.sqrt (A.B.a.clock.forcedAllowance m))
    scales : (mi).Radial (fun _=>1) ((T₁)*hc) ((T₂)* (Y^aust+Δ)) ((T₂)*0) (ν₀) ∧ (tι).Radial (fun _=>1) ((T₁)*hc) ((T₂)*(Y^aust)) ((T₂)*Δ) (ν₀)
-- `stepClean` automatically now. 
variable {t b Ra μ ζ kB r R₁ Q₁ J'}
variable (hζ:MintZ A.delay J₀ r)(hV:(μ+2)*kB + (-ζ) ≤ -J₀)
include hQ hζ hV hkz hμ hh hs
lemma conveyor (h: Pits H F x d0 Z L₀ (Cℓ) D' E' bw N' φ) (ht:OperaZ H k F W k' W' x d0 Z hk L₀ Cℓ D' E' bw v N' φ hc) : Passage H k F W k' r b kB Ra μ ζ x hc L₀ X' FL d0 Z hk R₁ Q₁ v N' φ:=by
    have hi:= hQ.entry; have hp:=hQ.outlet
    have h': V! =  R₁:= by rw [Embrasure.click _ _ hi]; exact hQ.inlet
    have hg: ∀ i: Config G A₀,(Qo).push R₁.beta (Cℓ).density i=(tι).density i:=by
       intro i; rw [show R₁.beta= (V!).beta from congr_arg _ h'.symm]; exact ht.trueM i
    let vH:=(Cℓ); let FX:= mi; let F':= tι; have hw:1 ≤Y:=(H.vote.cash _ _ (step_paid (A.B.a) m)|>.2 _ (A.B.valid.pays m)).light.1
    have hx(i): vH.density i= (R₁.eval i:ℂ) • Marker.Poly.pass (Extra.Trajectories.Layers.logPart (X'.baked R₁ L₀ b) i):=by
       rw [← h']; exact hh.authentic _
    have hy: (Qo).push R₁.beta R₁.eval 1= Real.exp ((Q').v* Fintype.card (Site A₀)):=by rw [hp]; exact hQ.charge
    refine ⟨h',hp,h,ht,hx,hg,fun i=>?_ ,?_,?_⟩
    · rw [hy]; exact sheared _ _ _ _
    · have hu:= ht.error; rw [hkz] at hu; apply Port.fenestrated _ kB hs Y μ hμ hw hu J₀ hV
      have hz:= (F.turns x hi).2; rw [hQ.inlet] at hz; unfold RG.Shoot.band at hz; rw [beta_eq A.B.valid] at hz
      exact hζ _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) R₁.beta hz.1 hz.2
    obtain ⟨hP,hT⟩:=ht.spent; rw [hkz] at hT hP; exact ⟨Port.honours _ kB hs Y μ hμ hw hT,Port.honours _ kB hs Y μ hμ hw hP⟩ -- definitional tag O.User syntax
end Career
end YM.PhysicalNext.Repeat.Mallow
