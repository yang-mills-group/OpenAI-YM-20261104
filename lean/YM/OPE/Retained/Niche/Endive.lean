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
noncomputable abbrev forecast := Whit (Reach (A:=A) m) (D.stream l) (hazard (D.stream l) he) (show l+6 ≤ l+6 from le_rfl) (A.B.a.clock.hatBeta m)
def RequestK :Prop:= (forecast g D (he:=he)) ≤ (A.B.a.S.side m p).val
local notation "x0!"=>A.B.a.clock.hatBeta (m+1)
lemma DemandC:∀ᶠ p:ℕ in atTop,Lac A m p ∧ RequestK (p:=p) g D he:= (step_lit A.B.a m).and ((Stationary.bound_climb G (A') m).eventually_ge_atTop _)
local notation "A0"=>(Labels.frames G).level l
local notation "ρ"=> pursuit g D he
variable (hu:Lac A m p)
local notation "pΦ"=> PadQ H ζP
local notation "Φ"=> berthQ C h hs g hm hu
noncomputable abbrev Portα :=(OarX (d:=l) W hy (Nat.lt_trans (Nat.lt_succ_self _) hm) p).toContinuousLinearMap
include hx hn Yq
local notation "TC"=> s.profile (J m)
local notation "TF"=> s.profile (J (m+1))
local notation "WT"=> D.OAuth l (J (m+1)) ρ
local notation "WV"=> D.OAuth l (J m) he
local notation "Uμ"=> D.stream l
local notation "SP"=> BootU A.θ F.books (Austen C F g hm hn Yq)
local notation "F*"=> ζP
local notation "HΩ"=> slender jν
noncomputable abbrev TellerZ := YieldP (A0) ((F*)).L (TF)
include he in
lemma AutoC : ∃ q:Pillar SP Φ x0, Aud SP Φ TF TC x0 q:= Realty C F h hs g hm hn hu Yq ((FuelZ F g D R he hx).1)
variable (hk:RequestK (p:=p) g D he)
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
lemma paidZ : AuraP (hz:=he) (V:=pΦ) (F:=localSection G l) (X₀:=hol G) (v:=slender (J (m+1))) (Ta:=TF) (Tx:=TC) R Uμ WT WV SP (YieldP (A0) (ζP).L (TF)) x0:=
       (FuelZ F g D R he hx).2 (Austen C F g hm hn Yq)
omit hx hn Yq
local notation "YB"=> YieldP (A0) (ζP).L (TF)
lemma revenueZ: ‖Portα C Q X W hy hm (p:=p)‖≤ YB:=by
        have hv:= Singer (d:=l) (p:=p) (m:=m) W hy (show m<N from Nat.lt_trans (Nat.lt_succ_self _) hm); change ‖Portα C Q X W hy hm (p:=p)‖≤ YieldP (A0) (A.B.a.S.block m) (A.B.a.params (m+1)) at hv; rw [depQ,params_eq A.B.valid] at hv; exact hv
include hu
lemma κEpic : let Z':= (Stepm (d:=l) W (m:=m+1) (hy.trans (Nat.le_succ m)) hm.le p); let M:= (Stepm (d:=l) W (m:=m) hy (by exact (Nat.le_succ m).trans hm.le) p (N:=N)); ∀ v: (A0).Coeff,(M (Portα C Q X W hy hm (p:=p) v)).density 0 (localSection G l) (C.history N p m)=(((Reach (A:=A) m).L.val:ℝ)^l) • ((Φ).hostS.Z.push ((Φ).pW.beta) ((Z' v).density 0 (localSection G l) ((Φ).pW))):=by
        intro P M v; change _= _ • ((SlotF (K:=H) (ηSz A m p)).push _ _); rw [canyon hs, ←depQ]; exact pools W (d:=l) hy (Nat.lt_trans (Nat.lt_succ_self _) hm) (p:=p) v
end Story
end YM.OPE.Owl.Retained

