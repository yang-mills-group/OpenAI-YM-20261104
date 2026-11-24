import YM.MSbar.Ballet.Vols
import YM.MSbar.Fiber.Frost
import YM.MergeProof.Almandine

/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
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
-- Can use for other payments. order pressure. Extant reading‐Z every point, Tied Stories mongoose.Beta.
set_option quotPrecheck false
variable {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}
variable (b:Bandage X C K)(Q:ℕ→ℕ)(T:Bolt A)(t:ℕ→ℕ)(Y:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail T) N p)
    (D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m))(hx:Chateau b Q T t Y D)
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
lemma floorsP (hi:m≤N) :(R m).path=A.B.kin.path N m :=by change (T.history N p m).path=_; rw [((T.sticks N p).prices m (Nat.zero_le _) hi).1.path,A.B.bases]
variable (hr: Mallow.Hoard X.shape A.delay)(u:G.ColorIndex)
variable (p' s:ℕ)
variable (ht:YM.MSbar.Alto.Reports M.K M.p M.O A.B.a)(hz:YM.MSbar.Ballet.Load M.K M.p.kernel M.O A.B.a u W)
variable (hX:∀ m',A.B.a.clock.hatBeta (m'+1) ≤ 2*A.B.a.clock.hatBeta m')
variable (hV:∀ m' i,YM.MSbar.Mosaic.hatW (A.B.a.clock.hatBeta m')^4 ≤(A.B.a.S.side m' i).val)
variable (hO:Tendsto (fun m=>(A.B.a.params m).order) atTop atTop)(hP:p'+2 ≤ m)
include hG hP
lemma seedP :∀ᶠ N:ℕ in atTop, ∀ i:ℕ,let R₀:=(Issue.trail T).rep N i N; let x:=A.B.a.S.side N i; YM.MSbar.Ballet.Ticket (t! N) x (θ R₀ (opening G x) (cue R₀.beta) p') s p' m:=by
    let v(i):=A.B.a.clock.hatBeta i
    have hv : Tendsto v atTop atTop:= tendsto_atTop_add_const_left _ _ (A.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
    let E(j i:ℕ):= H|>.rep j i j; let f(i j):= cue (E i j).beta
    have hh :∀ᶠ i in atTop,∀ j:ℕ,True→ YM.MSbar.Ballet.Ticket (v i) (A.B.a.S.side i j) (YM.MSbar.Ballet.starP (f i j) p' (widthV G (A.B.a.S.side i j))) s p' m:=by
          apply YM.MSbar.Mosaic.cofy; intro g a he hp;
          have hX:Tendsto (fun x=> v (g x)) atTop atTop:= hv.comp he
          let t(i):=f (g i) (a i); have hB : YM.MSbar.Mosaic.Run atTop (fun i=>v (g i)) t (-(1/2)):=by
              apply (fun h=> YM.MSbar.Mosaic.charges hX (f:=t) h|>.1); filter_upwards [hX.eventually_gt_atTop 0] with i hi; obtain ⟨h,hQ⟩:= T.choice.represents (g i) (a i) _ le_rfl|>.band; exact YM.MSbar.Mosaic.ever hi h hQ
          apply (YM.MSbar.Ballet.grown (G:=G) _ m s hP hX hB (Eventually.of_forall fun i=> inv_pos.mpr (Real.sqrt_pos.mpr (YM.MSbar.Ballet.betaP H T.choice (g i) _ (g i) le_rfl)))).mono
          intro i h; exact h _
    filter_upwards [hh] with i hi j; let R₀:=E i j; let x:=A.B.a.S.side i j; intro
    have hK(l:ℕ)(he:l≤2): SameJet l (fun u=>Wilson.energy (Precision.represent u:Config G x)) (main x R₀.clip R₀.path):=by
       have hg:=A.B.support.peak i j l (by omega)
       rw [show R₀.clip=(A.B.a.params i).clip from (T.choice.represents i j i le_rfl).clip, show R₀.path=_ from floorsP T i j i le_rfl]; exact ⟨hg.2.1,hg.1,hg.2.2.symm⟩ -- names
    have hp:= YM.MSbar.Ballet.betaP H T.choice i j i le_rfl; let g:=f i j; have hh:θ R₀ (opening G x) g p'=YM.MSbar.Ballet.starP g p' (widthV G x):=by
          funext u'; have he:=pruner R₀ g p' u' hK (inv_pos.mpr (Real.sqrt_pos.mpr hp)) (show g⁻¹ ^2= R₀.beta from (by unfold g f YM.MSbar.Heath.Stock.cue; rw [inv_inv,Real.sq_sqrt hp.le])) (T.choice.starts i j|>.2); exact he
    change YM.MSbar.Ballet.Ticket (t! i) _ (θ R₀ (opening G x) g p') s p' m; rw [hh]; exact hi j True.intro
include hO hx ht hz hX hV hr
-- Recurrence coherent for all orders at finite-tor. Scene independent actual.I.Budget.Pure.Ports. 
lemma sceneP (hS:6 ≤ s)(hh:4 ≤ m) : ∀ᶠ k:ℕ in atTop,∀ N i:ℕ,∀ S:Scene A.B.a i p',Realized A.B.kin N i k p' (YM.MSbar.Lis.sun G u) S→
     (∀ j,k ≤ j→ j ≤ N → let Q':=(Issue.trail T).rep N i j; YM.MSbar.Ballet.Ticket (A.B.a.clock.hatBeta j) (A.B.a.S.side j i) (θ Q' (S.Poly j) (cue Q'.beta) p') s p' m) ∧∀ j,k≤j → j<N→|cue ((Issue.trail T).rep N i j).beta/ cue ((Issue.trail T).rep N i (j+1)).beta - taste p' (S.action j) (cue ((Issue.trail T).rep N i j).beta)|≤ YM.MSbar.Mosaic.goalP (A.B.a.clock.hatBeta j) p' :=by
   obtain ⟨V,hb⟩:= eventually_atTop.mp (seedP T m hG p' s hP); have hv:=townsR b Q T t Y D hx
   have hm':=YM.MSbar.Alto.skyline A.B p' hG ht hv s u hS
   filter_upwards [hm',A.B.a.fits.deep.eventually_ge_atTop (max s m),hO.eventually_ge_atTop (m+1), eventually_ge_atTop V] with k hx' hi hk hK N i S h₀
   let F:= (Issue.trail T).rep N i
   let g(j):= cue (F j).beta
   let P₀(j):= YM.MSbar.Ballet.Ticket (A.B.a.clock.hatBeta j) (A.B.a.S.side j i) (θ (F j) (S.Poly j) (g j) p') s p' m
   have hh'(j)(h₁:k≤j)(h₂:j<N)(hy:P₀ (j+1)) : P₀ j ∧|g j/g (j+1)-taste p' (S.action j) (g j)| ≤ YM.MSbar.Mosaic.goalP (A.B.a.clock.hatBeta j) p':= by
       have hT:= T.choice; apply YM.MSbar.Ballet.palette A.B u W N k j i p' m s S h₀ _ _ (auditorium b Q T t Y D hx W N i j h₂ hG hX (fun k=>hr _ _ (A.B.valid.pays k) _ (step_paid A.B.a k))) (floorsP T N i _ h₂) (floorsP T N i _ h₂.le) ((hx' N i S h₀).1 _ (by omega) h₂) hS hh hP (hi.trans (A.B.a.fits.mono (show k ≤ j+1 from by omega))) _ (YM.MSbar.Ballet.validP H T.choice hv.towns N i _ h₂ |>.1) h₁ h₂ hG hz ht hv hy (hV _ _) (hV _ _); rw [show (F j).p=A.B.a.budget j from (T.choice.represents N i _ h₂.le).vac]; exact hk.trans (A.B.a.fits.deepOrder h₁)
   have hp(j:ℕ)(he:j ≤ N)(hh:k ≤ j) : P₀ j :=by
       induction he using Nat.decreasingInduction with
       | self=> unfold P₀;rw [h₀.opening]; exact hb _ (hK.trans hh) _
       | of_succ j he ih=> exact hh' j hh he (ih (by omega))|>.1
   exact ⟨fun j hi hv=> hp _ hv hi, fun j hh he=> hh' j hh he (hp (j+1) he (by omega)) |>.2⟩
end YM.PhysicalNext.Repeat.Legato
