import YM.OPE.Compatible.Niche.Mine
import YM.OPE.Retained.Niche.Endive
import YM.OPE.Retained.Niche.Jubilee
import YM.OPE.Retained.Niche.Boson
import YM.OPE.Compatible.Niche.Pique

/-! The physical OPE estimate on the retained kinetic horizon and transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl.Retained
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ ThroughLaunch Zeph
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι :Type} {G :Gauge} {P: MapPrices}
variable {P':Patch}{n N i j m p l:ℕ}{H:Sponsor G}{T:Seasons H}{s:Sheet G}{t:ℕ→ℕ}
section Story
open Next.Foundations
open Source
local notation "MG"=> ThroughLaunch.bountyV s P t
variable {S:Supply.Rolls (ThroughLaunch.raise s t)}{A:Alloy (ThroughLaunch.bountyV s P t) S}(C:Bolt A)(F:Factor A) (Q:ℕ→ℕ) (X:∀ d N p,TransferData ((Labels.frames G).level d) (Extra.Histories.Issue.trail C) N p)
local notation "E"=>A.B.a.clock
local notation "J"=>A.B.a.clock.J
local notation "jν"=> J (m+1)
local notation "ξ"=>A.B.a.S
set_option quotPrecheck false
local notation "ζP"=> Reach (A:=A) m
local notation "ν"=>A.B.kin.alpha
local notation "C!"=>Family.mk (Extra.Histories.Issue.trail C) (hol G) (Labels.frames G) (localSection G) Q X
variable (W: Family.Makes (Family.mk (Extra.Histories.Issue.trail C) (hol G) (Labels.frames G) (localSection G) Q X))
variable {Z: LocalRatio (chart G)}{L:PriceBook Z T}{a:Axis}
variable (h: Imperial (s:=s) H.X P H.l A.post A.B.a A.B.M A.B.kin)(hs:Lend s T)(g:G.Simple)(D:Desk (ThroughLaunch.raise s t) L a g)(R:Spells.Pad G)
local notation "S!"=> A.B.a.clock.op m p
local notation "x0"=> A.B.a.clock.hatBeta m
local notation "A'"=> A.B.a
variable (he: D.cost l ≤ A.B.a.clock.J m)(hx: BeatV D R A.θ F.books A.delay)
variable {Y:ℕ→ℝ}{z:Bid.Worth}(Yq:Bandage F Y z)
variable (hn:Nest F C)(hy:Q l ≤ m)(hm:m+1 < N)
local notation "A0"=>(Labels.frames G).level l
local notation "ρ"=> pursuit g D he
variable (hu:Lac A m p)
local notation "pΦ"=> PadQ H ζP
local notation "Φ"=> berthQ C h hs g hm hu
include hx hn Yq
local notation "TC"=> s.profile (J m)
local notation "TF"=> s.profile (J (m+1))
local notation "WT"=> D.OAuth l (J (m+1)) ρ
local notation "WV"=> D.OAuth l (J m) he
local notation "Uμ"=> D.stream l
local notation "SP"=> BootU A.θ F.books (Austen C F g hm hn Yq)
local notation "F*"=> ζP
local notation "HΩ"=> slender jν
local notation "hc"=>(Nat.lt_trans (Nat.lt_succ_self _) hm)
local notation "M!"=> Portα C Q X W hy hm (p:=p)
variable (hk:RequestK (p:=p) g D he)
variable (V:Tail (m:=m) C Q X W hy (p:=p) (Nat.lt_trans (Nat.lt_succ_self _) hm))(V':Tail (m:=m+1) C Q X W (hy.trans (Nat.le_succ m)) (p:=p) hm)
local notation "tA"=> A.B.a.clock.hatBeta (m+1)
local notation "S₀"=> localSection G l
local notation "VF"=>Scan C Q X W h hs g D R he hy hc (p:=p) V
local notation "FV"=> Scan C Q X W h hs g D R (pursuit (m:=m) g D he) (hy.trans (Nat.le_succ m)) hm (p:=p) V'
variable (hV:Festival (p:=p) C Q X W h hs g D R he hy (Nat.lt_trans (Nat.lt_succ_self _) hm) V)(hv:Festival (p:=p) C Q X W h hs g D R (pursuit g D he) (hy.trans (Nat.le_succ m)) hm V')
include hk hu hV hv
set_option maxRecDepth 4096
set_option maxHeartbeats 200000 in
lemma Fruition : Plasma Uμ (dims Uμ) (A.B.a.S.block m) (κBit Uμ) x0 tA HΩ M! FV VF:=by
       rw[depQ]; exact ℰThunder (V:=pΦ) (Ta:=TF) (Tx:=TC) (X₀:=hol G) (F:= S₀) (y:=tA) (x:=x0) (w:= YieldP (A0) (ζP).L (TF)) (P0:=SP) (Pf:=Stepm W (d:=l) (m:=m+1) (hy.trans (Nat.le_succ m)) hm.le p) (Pc:=Stepm W (d:=l) (m:=m) hy (le_trans (Nat.le_succ m) hm.le) p) R Uμ WT WV Φ V' V M! hv.face.2 hV.face.2 (revenueZ C Q X W hy hm) (paidZ C F g D R he hx Yq hn hm) (AutoC C F h hs g D R he hx Yq hn hm hu) PassF hk (κEpic C Q X W h hs g hy hm hu)
omit hk hu hV hv
include h hs X W hy
lemma Concordia : ∀ᶠ p:ℕ in atTop,∀ N:ℕ,∀ U:m+1<N,∀ (Φ0 :Tail C Q X W (hy.trans (Nat.le_succ m)) (p:=p) U) (Φ1:Tail C Q X W hy (p:=p) (Nat.lt_trans (Nat.lt_succ_self _) U)), Festival C Q X W h hs g D R (pursuit g D he) (hy.trans (Nat.le_succ m)) U (p:=p) Φ0 → Festival C Q X W h hs g D R he hy (Nat.lt_trans (Nat.lt_succ_self _) U) (p:=p) Φ1 → Plasma (D.stream l) (dims (D.stream l)) (A.B.a.S.block m) (κBit (D.stream l)) x0 tA HΩ (Portα C Q X W hy U (p:=p)) (Scan C Q X W h hs g D R (pursuit g D he) (hy.trans (Nat.le_succ m)) U (p:=p) Φ0) (Scan C Q X W h hs g D R he hy (Nat.lt_trans (Nat.lt_succ_self _) U) (p:=p) Φ1):= by
       filter_upwards [DemandC g D he] with p hi N h Φ0 Φ1 hU hV; exact Fruition C F Q X W _ hs g D R he hx Yq hn hy h hi.1 hi.2 Φ1 Φ0 hV hU
end Story
end YM.OPE.Owl.Retained

