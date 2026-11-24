import YM.AllOrder.Horizon.FirstStep
import YM.AllOrder.Plateau.Unique
import YM.AllOrder.Plateau.Job

/-!
# Kernel m+1→m probe for model approximation of the interacting physical density

Theory fixed at the strongest family. Body on true pure input, with explicitly
qualified calls available also for other representations on whole β intervals.
Full all-good cylinder analysis and full fields-density local norm exposed via
Credits. Support compression & critical width included. No claim yet of repeated
iteration matching along C (which adds E and computes shifts).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Line
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext Repeat Height Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Shop Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X : Metals G} {D:Rolls X.p} (A : Alloy X D) (F:Factor A) {c f : Side} {n m N k : ℕ}
open Ker Ker.Start Haiku Kinetic.Port Fire PertExtension.Series Radial Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sienna Coat Push.Uniform Brush BudgetPoint
variable {β:ℝ}
set_option quotPrecheck false
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
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
local notation "hJ" => (A.B.a.clock.adm (m+1))
local notation "hp" => (A.B.a.clock.adm m)
local notation "K"=> X.p.kernel
local notation "Π"=> A.B.a.S.block m
local notation "s" => Mural.sheet X.p D hJ
local notation "W" => X.p.profile J
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)
local notation "R₁"=> A.B.kin.path N (m+1)
local notation "R₂"=> A.B.kin.path N m
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "D₀"=>ConnectedActivityE6.loopBill G L x₀
local notation "H'"=> Shop.Pledged -- not yet
local notation "Γ"=> precinct D (i:=I) hJ
local notation "M"=> Bank D (i:=I) hJ
variable (π:f.val=c.val*(A.B.a.S.block m).val)(hβ:β∈band A.B.a (m+1))(hk:m<N)
local notation "S"=>Pane.panel A m π
local notation "T"=> orchestra A N π
variable {r:ℕ} (U:Bank (i:=A.B.a.clock.J m) D (A.B.a.clock.adm (m+1))) (hx: Plus D F.target (A.B.a.clock.adm (m+1)) U (A.B.a.clock.hatBeta m))
    (t:precinct D (i:=A.B.a.clock.J m) (A.B.a.clock.adm (m+1))) (h: Books A (m:=m) (N:=N) t) (hr:r ≤ A.B.a.clock.J m)
local notation "Z'"=> z^Shop.air I
local notation "M'"=> Plateau.shelter U.reps t (gStep β) B r c
local notation "Λ₀"=> (fun i:Γ=> i.paid)
local notation "b₀"=> (Plateau.Line.laurels D (i:=I) (j:=J) x₀)
local notation "η₀"=>Line.sage D (i:=I) (j:=J) x₀
local notation "η"=> Line.laurels D (i:=I) (j:=J) x₀
local notation "F₁"=> beacon_star (c:=c) A F U t β r
local notation "Λ₁"=> (clock_pure A F (m:=m))
local notation "Λ₂"=> silk A F U t β r
local notation "Λ"=> (fun (i:Γ)=> i.paid)
local notation "ε"=> z^ (output r (4*edgeW I))
local notation "e"=> Trio.base Y B
variable (H:Shop.Pledged A F)
include H
/-- choose one Folio per stage edge, independent of halt and physical reps.
The kiosk at real-combined Family with plateau post proofs has even stronger
∃ per Shape once any stage; this call for a level. -/
lemma can_book : ∃ U:Bank D (i:=I) hJ, ∀ z'≥ A.delay.betaEntry J,Plus D F.target (A.B.a.clock.adm (m+1)) U z':= by
 obtain ⟨x,hx⟩:= Line.accounting A F (N:=m+1) (show m< m+1 from (by omega)) H.1
 exact H.2.2.2 _ _ (step_paid A.B.a m) hp hJ ⟨x⟩
local notation "Qℓ"=> (virgin T (A.B.a.budget (m+1)) β)
local notation "Y₀"=> z^air I
-- Full physical-window portability. Kernel held on actual stencils and masks here.
structure Drapery (U₀:Bank D (i:=I) hJ)(t: precinct D (i:=I) hJ)(h:LineCare N m A F β)(Q: Chartlet F.shape A N m π (virgin T (A.B.a.budget (m+1)) β)) :Prop where
    booked : Books A (N:=N) (m:=m) t
    seek : SeekR F.shape A N m π Q
    chosen : ∀ᶠ k in atTop,∀ r≤ A.B.a.clock.J m, Line.Credit A F π U₀ t (virgin T (A.B.a.budget (m+1)) β) Q h r k
-- preserve α pending.Expected.Full V boundary.
include H hβ hk h hx
lemma preserve (hc:2*e < c.val): Nonempty (LineCare N m A F β) ∧ ∀ W':LineCare N m A F β, ∃ Q, Drapery A F π (β:=β) U t W' Q:=by -- need "e"
  refine ⟨buyings A F hk hβ,fun W'=>?_⟩
  obtain ⟨Q,hQ⟩:= Pane.affords A N π hk (show 100*(1+radiusB x₀) ≤ c.val from (by unfold Trio.base Trio.tent at hc; omega)) F.shape F.pledging.conducts.income.grow.1 F.pledging.conducts.full hβ
  refine ⟨Q,h,hQ, Line.pearls A F π hβ hk U hx t h H.1 H.2.2.1 H.2.1 hc Qℓ rfl Q hQ W' rfl rfl (fun i=>rfl)⟩
omit hβ hk h hx in
lemma look (B₁ : Org.Bolt A): ∀ m, ∃ U: Bank D (i:=A.B.a.clock.J m) (A.B.a.clock.adm (m+1)), Plus D F.target (A.B.a.clock.adm (m+1)) U (A.B.a.clock.hatBeta m) ∧ ∀ N, m < N → ∃ t: precinct D (i:=A.B.a.clock.J m) (A.B.a.clock.adm (m+1)), ∀ n, let β := (B₁.history N n (m+1)).beta; let P' := ((A.B.a.S.oneStep m n).exact_size); ∃ V': LineCare N m A F β, ∃ X : Chartlet F.shape A N m ((A.B.a.S.oneStep m n).exact_size) (Pane.virgin (Pane.orchestra A N ((A.B.a.S.oneStep m n).exact_size)) (A.B.a.budget (m+1)) β), Line.Drapery A F P' U t V' X := by
  intro m'; obtain ⟨U,hU⟩:= Line.can_book A F (m:=m') H
  have hu:= hU _ (A.B.valid.pays m'); refine ⟨U, hu,fun N hN=> ?_⟩
  obtain ⟨t,h⟩:= Line.accounting A F hN H.1; refine ⟨t,fun n=>?_⟩
  intro β P'; have hh:β∈band A.B.a (m'+1):= ((B₁.sticks N n).prices (m'+1) (Nat.zero_le _) hN).2
  obtain ⟨hW,L'⟩:= Line.preserve A F (m:=m') P' hh hN U hu t h H (room_full A F (m:=m') (n:=n) H.1); let W':= Classical.choice hW; exact ⟨W',L' W'⟩
end YM.AllOrder.Plateau.Line
