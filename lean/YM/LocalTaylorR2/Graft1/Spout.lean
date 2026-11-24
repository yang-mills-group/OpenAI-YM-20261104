import YM.LocalTaylorR2.Grafting.Assist
import YM.LocalTaylorR2.Graft1.Stream
import YM.LocalTaylorR2.Calendar
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Floret
import YM.RG12.Joint.MeasureLimit
/-!
 # Next legislation for Taylor and K at the ACTUAL mark paths.
 Cash. all sup-port prices on same H.V. Terms before Tare, assembly at real Post.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
open Mallow Blush Lattice Daisy Lotus Daisy.Charity.RG12 UVNext.CouplingReset Extra.Histories Next.Foundations Planned.GuardedAtom
variable {G:Gauge}
-- `cD` content.Extra after one strict conversion d modeled within exact F0. give example ability to pay arbitrary powers of setup incl orientations (explicit)
def keyD (G:Gauge) : Daisy.Charity.RG12.Decal G where
  rub P Q E L W μ o U j x:= (∃ D:RG.Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j)→ ∀ l≤ j, ∀ k≤ j, Trailer Q E L W μ x o U.order U.power l Chi.canonical (CalendarStep.loss j) (fee G L U k)
  good P Q E:= by
    obtain ⟨n,h⟩:= missive P Q E; refine ⟨n,fun L hL W μ o U j _ hw hμ=>?_⟩
    by_cases he: ∃ D:RG.Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j; swap; · exact Eventually.of_forall fun _ hi=> (he hi).elim
    have hk(p k : ℕ):= (h L hL).2 W μ o U.order U.power p Chi.canonical (CalendarStep.loss j) (fee G L U k) (by unfold CalendarStep.loss; positivity) hw hμ he
    filter_upwards [eventually_all.mpr (fun i:Fin (j+1)=> eventually_all.mpr (fun p:Fin (j+1)=> hk i p))] with x ht _ l hl k hu using ht (⟨l,Nat.lt_succ_of_le hl⟩:Fin _) (⟨k,Nat.lt_succ_of_le hu⟩:Fin _)
variable {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j N n d:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (keyD G) R.shape A.delay) {l v:ℝ}
    (hG:G.Simple) (hm:m<N) {Q: In A.B.a m n} (H:Spring R N m n l v Q)(x:Set.Icc l v)
    (t:Cloud (Q x))(s:Site (A.B.a.S.side m n))(ν:ℂ) {u₀:ℕ→ℝ}{V:Bid.Worth}(Y:PhysicalNext.Repeat.Legato.Bandage R u₀ V)
local notation "P" => A.B.a.clock
local notation "T" => A.B.a.params m
local notation "b" => A.B.a.budget m
local notation "w"=>authors A.B.a m
local notation "χ" => A.B.a.clock.hatBeta m
local notation "x'"=> A.B.a.clock.hatBeta (m+1)
local notation "ω"=> A.B.a.clock.forcedAllowance m
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "s!"=> A.B.a.S.side m n
local notation "W"=> houseS H x
local notation "Θ"=> R.shape.μ Jp Ip
local notation "L₁"=> D.L Jp
local notation "Z'"=> scope W t s
set_option quotPrecheck false
local notation "π'"=> localSection G d
local notation "F'"=> (Labels.frames G).level d
local notation "R2" => H.result x
local notation "Pp" => (R.target Jp Ip)
local notation "Oo"=> (A.B.a.clock.op m n)
local notation "p0"=> pupil H x t.live
local notation "p1"=> pupil H x t.pale
local notation "Vc"=> plaque (p0) (p1) ν

variable (hd:d ≤ A.B.a.clock.J m) (h:s∈ t.live.crest.image (A.B.a.clock.op m n).ratio.parent) {ε:ℝ}
include hp hd

local notation "FF!" => fee G (D.L Jp) (A.B.a.params m) d
local notation "Mk"=> markBill t.live Pp
local notation "Mk0"=> CalendarStep.loss Jp
-- call on all guides, not assuming particular pedigree.C.
lemma plenty {R' : Rep G (A.B.a.S.side (m+1) n)} (p:ℕ)(hi:p ≤ Jp)(U:Guide A.B R.shape N m n R'): Trailer Pp (R.expense Jp Ip) L₁ (R.walls Jp Ip) Θ χ (R.shape.o Jp Ip) (b).order (b).power p Chi.canonical Mk0 FF! := by
   let V:= M.p.profile Ip; have h:=U.laws.data.funds
   change Trailer _ _ _ _ _ _ _ (T).order (T).power _ _ _ _; rw [params_eq A.B.valid]
   exact hp _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) ⟨(Oo).patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩ p hi d (hd.trans (step_paid A.B.a m).1)

variable (hp': Mallow.RG12.Earned (roadD G) R.shape A.delay) {f':ℝ} (w':Reel.Scroll G (A.B.a.S.side (m+1) n)) (hf: Reel.Affords (Q x) A.B.a (m+1) w' f')
local notation "δ!"=> (2*x'^(21/10:ℝ)*f')
include hf hp' h hm
lemma roadwayBudget {i p:ℕ}(take':(houseS H x).fragrances→ℕ→Prop)(hN:p ≤ Jp)(he:i≤p)(hF:∀ x k,take' x k→ i ≤ k ∧ k ≤ p):
    let e':=x'^requested i Mk0
    let ξ:= highway W t take' ν w' p
    Modesty G (R2).p s Z' ξ (flash (d:=d) R x t ν e') ∧ Modesty G (R2).p s Z' (sheetC W t take' ν p-ξ) (flash (d:=d) R x t ν (δ! *e')) := by
   have hV: (b).supportExponent+2 ≤ (R.expense Jp Ip).earn:= by rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith only [R.pledging.agenda _ _ (step_paid A.B.a m)|>.1]
   let D' :=localSection G d; let t':=(P).allowance (m+1)/(2*f'); let g:=(Q x); let S:=t' • (w'-g.activities.E); let y (t:Reel.Strand):= g.activities.E + Reel.Strand.dial t • S
   have hb:=plenty R hp hd p hN W; let hc:= H.knows x x.2
   have hΨ (t:Reel.Strand):PartialLives A.B.bake N (m+1) n (Reel.bend g (y t)):= ⟨hc.1.path,hc.1.point,hc.1.clip,hf.stamps t⟩
   choose H' hA using fun t=> Opera.partial_feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income (hΨ t) (show (Reel.bend (Q x) (y t)).beta∈_ from hc.2)
   obtain ⟨u',hu',hv,hs⟩:= Reel.blend_it hf; change y u'=w' at hs
   intro e ξ
   have he : i≤ p+1:=he.trans (Nat.le_succ p); let hc:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n)
   have hh : Modesty G (R2).p s Z' (sheetC W t take' ν p- (highway W t take' ν (y u') p)) (flash (d:=d) R x t ν ((Reel.Strand.spelling p * Reel.Strand.dial u') * e)):= by
       unfold flash e; rw [beta_eq A.B.valid]; exact Marker.towP W t take' ν s S hb (uncoupled ..) hc hV rfl rfl i he (fun u q h=> (hF u q h).1) h (fun u q h=> (hF u q h).2) u' H' hu' -- rw beta equality in S??
   unfold ξ; rw [← hs]; refine ⟨?_,Modesty.rise hh (Marker.monotonicF (d:=d) R x t ν ?_)⟩
   · unfold flash e; rw [beta_eq A.B.valid]; exact Marker.surrender W t take' ν s (y u') hb (uncoupled ..) hc hV rfl rfl i he (fun u q h=> (hF u q h).1) h (H' u')
   rw [hv]; exact mul_le_mul_of_nonneg_right (Many.numericWidth (m:=m) (R:=R) p hp' hN f' hf.leftB.le).1 (Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _)

-- alpha.Errs application; combine after computing both Raw receipts
end YM.LocalTaylorR2.Marker
