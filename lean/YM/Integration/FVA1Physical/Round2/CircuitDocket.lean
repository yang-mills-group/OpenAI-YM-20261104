import YM.Integration.FVA1Physical.Round2.CircuitSeason

/-! Build the full vacuum analytic docket on the same C18 marked-field family. The induction uses the witnessed C18 input and its measured coupling at each step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

variable {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}
    {T:Bolt A} {l : ℕ} (g : Bandage.Harmonics X C K T l)
    (room : coarseRoom M P A X)
variable (W:YM.MSbar.Heath.Voice G)
variable (N p m:ℕ)(hm:m<N)(hG:G.Simple)
local notation "R"=> (Issue.trail T).rep N p
local notation "L"=> A.B.a.clock
local notation "H"=> Issue.trail T
open YM.MSbar.Midpoint YM.MSbar.Rolling
open YM.MSbar.Bakery Pressure YM.MSbar.Bakery.Portal
local notation "t!"=> A.B.a.clock.hatBeta
local notation "cue"=> YM.MSbar.Heath.Stock.cue
local notation "θ"=> YM.MSbar.Aqua.film
variable (hr: Mallow.Hoard X.shape A.delay)(u:G.ColorIndex)
variable (p' s:ℕ)
variable (ht:YM.MSbar.Alto.Reports M.K M.p M.O A.B.a)(hz:YM.MSbar.Ballet.Load M.K M.p.kernel M.O A.B.a u W)
variable (hX:∀ m',A.B.a.clock.hatBeta (m'+1) ≤ 2*A.B.a.clock.hatBeta m')
variable (hV:∀ m' i,YM.MSbar.Mosaic.hatW (A.B.a.clock.hatBeta m')^4 ≤(A.B.a.S.side m' i).val)
variable (hO:Tendsto (fun m=>(A.B.a.params m).order) atTop atTop)(hP:p'+2 ≤ m)
include hG hP hO g room ht hz hX hV hr in
-- Recurrence coherent for all orders at finite-tor. Scene independent actual.I.Budget.Pure.Ports. 
lemma circuit_scene (hS:6 ≤ s)(hh:4 ≤ m) : ∀ᶠ k:ℕ in atTop,∀ N i:ℕ,∀ S:Scene A.B.a i p',Realized A.B.kin N i k p' (YM.MSbar.Lis.sun G u) S→
     (∀ j,k ≤ j→ j ≤ N → let Q':=(Issue.trail T).rep N i j; YM.MSbar.Ballet.Ticket (A.B.a.clock.hatBeta j) (A.B.a.S.side j i) (θ Q' (S.Poly j) (cue Q'.beta) p') s p' m) ∧∀ j,k≤j → j<N→|cue ((Issue.trail T).rep N i j).beta/ cue ((Issue.trail T).rep N i (j+1)).beta - taste p' (S.action j) (cue ((Issue.trail T).rep N i j).beta)|≤ YM.MSbar.Mosaic.goalP (A.B.a.clock.hatBeta j) p' :=by
   obtain ⟨V,hb⟩:= eventually_atTop.mp (seedP T m hG p' s hP); have hv:=circuit_merit room
   have hm':=YM.MSbar.Alto.skyline A.B p' hG ht hv s u hS
   filter_upwards [hm',A.B.a.fits.deep.eventually_ge_atTop (max s m),hO.eventually_ge_atTop (m+1), eventually_ge_atTop V] with k hx' hi hk hK N i S h₀
   let F:= (Issue.trail T).rep N i
   let actual(j):= cue (F j).beta
   let P₀(j):= YM.MSbar.Ballet.Ticket (A.B.a.clock.hatBeta j) (A.B.a.S.side j i) (θ (F j) (S.Poly j) (actual j) p') s p' m
   have hh'(j)(h₁:k≤j)(h₂:j<N)(hy:P₀ (j+1)) : P₀ j ∧|actual j/actual (j+1)-taste p' (S.action j) (actual j)| ≤ YM.MSbar.Mosaic.goalP (A.B.a.clock.hatBeta j) p':= by
       have hT:= T.choice; apply YM.MSbar.Ballet.palette A.B u W N k j i p' m s S h₀ _ _ (circuit_season g room W N i j h₂ hX (fun k=>hr _ _ (A.B.valid.pays k) _ (step_paid A.B.a k))) (floorsP T N i _ h₂) (floorsP T N i _ h₂.le) ((hx' N i S h₀).1 _ (by omega) h₂) hS hh hP (hi.trans (A.B.a.fits.mono (show k ≤ j+1 from by omega))) _ (YM.MSbar.Ballet.validP H T.choice hv.towns N i _ h₂ |>.1) h₁ h₂ hG hz ht hv hy (hV _ _) (hV _ _); rw [show (F j).p=A.B.a.budget j from (T.choice.represents N i _ h₂.le).vac]; exact hk.trans (A.B.a.fits.deepOrder h₁)
   have hp(j:ℕ)(he:j ≤ N)(hh:k ≤ j) : P₀ j :=by
       induction he using Nat.decreasingInduction with
       | self=> unfold P₀;rw [h₀.opening]; exact hb _ (hK.trans hh) _
       | of_succ j he ih=> exact hh' j hh he (ih (by omega))|>.1
   exact ⟨fun j hi hv=> hp _ hv hi, fun j hh he=> hh' j hh he (hp (j+1) he (by omega)) |>.2⟩

section
variable (t:ℕ→ℕ) (Y:∀ d N i,TransferData ((Labels.frames G).level d) (Issue.trail T) N i)
  (estate : Estate u W A.B)
include g room hr estate hG
theorem circuit_docket :
    Docket (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t Y) u M.O A.B.M A.B.kin := by
  refine ⟨fun N i m hm => floorsP T N i m hm, ?_⟩
  intro s r m hs hm hq
  have geo := circuit_merit room
  filter_upwards [circuit_scene g room W m hG hr u r s estate.levy estate.cart estate.sees estate.earns estate.holds hq hs hm,
      YM.MSbar.Alto.skyline A.B r hG estate.levy geo s u hs] with k ready width
  intro N i hN
  exact ⟨YM.MSbar.Alto.chosen A.B hG estate.levy geo N u r i hN,fun S hS =>
    ⟨(ready N i S hS).1,(ready N i S hS).2,(width N i S hS).1⟩⟩
end
end YM.PhysicalNext.Repeat.Legato.Round2
