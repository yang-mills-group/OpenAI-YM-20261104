import YM.LocalTaylorR2.King.Lore
import YM.LocalTaylorR2.Marker.Pad
/-! # actual `Uses` from Career. Campaign: every-order-in-interaction iteration of full **local E-data**, not of correlations. Holds actual K and parameters fixed channel, budgets every step. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.King
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
open Reel Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
variable {G:Gauge}
variable {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m N n:ℕ} (Ξ:Engine G)(R:Factor A) (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(hΞ:Mallow.RG12.Earned (survey Ξ.toRegime) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hq:Mallow.RG12.Earned (overD G) R.shape A.delay)  {g:G.Simple} (S:Uses R g)
     (p:ℕ)(hp:3 ≤ p)(ε:ℝ)(hε: ε≤1)(hm:m<N)
local notation "τ" => A.B.a
local notation "B" => A.B.a.budget m
local notation "h" => A.B.a.clock.hatBeta
local notation "K" => (S.realBeat 0 N n m)
local notation "Y" => (Marker.beam R S (n:=n) hm)
local notation "σ" => Orchard.beam0
local notation "u" => upfront (h m) p ε
local notation "u₀" => upfront (h (m+1)) p ε
set_option quotPrecheck false
-- router always dropping BOTH the ancestry residual & indicated Tail.
-- Keep genuine Crest/aux inputs. No fitting any coefficients.
-- Not mutated histories; (realBeat).activities.E only the top initialization at m=N.
include S -- def uses S, Lean linter
-- Termination.
def windward (N n:ℕ) (m:ℕ): Reel.Scroll G (A.B.a.S.side m n):= if hm:m<N then
    forest Ξ R (Marker.beam R S (n:=n) hm) Orchard.beam0 (windward N n (m+1)) p else (S.realBeat 0 N n m).activities.E
termination_by N - m
local notation "Ū" => windward Ξ R S p N n m
local notation "Z" => windward Ξ R S p N n (m+1)
local notation "A'"=> (Y).result σ
lemma winding : (Ū)=forest Ξ R Y σ Z p:=by rw [windward,dif_pos hm]
lemma attop : windward Ξ R S p N n N=(S.realBeat 0 N n N).activities.E:=by rw [windward,dif_neg (lt_irrefl _)]
local notation "v" => A.B.a.clock.allowance m
local notation "Φ"=> (A.B.a.clock.J (m+1))
variable (hΦ:p ≤ A.B.a.clock.J (m+1)) (hv:3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε)
lemma Inland.raise {w:Scroll G (A.B.a.S.side (m+1) n)} {x y:ℝ} (H:Inland Ξ R (Marker.beam R S hm) Orchard.beam0 w p x) (hx:x≤y) : Inland Ξ R (Marker.beam R S hm) Orchard.beam0 w p y:= ⟨⟨book_up H.estate.1 hx, book_up H.estate.2 (add_le_add_right hx _)⟩,fun c=>book_up (H.stakes c) (add_le_add_right (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) _),H.price,H.rooms,H.scalar.trans hx,H.beta.trans hx⟩
variable (Gq:Affords (S.realBeat 0 N n (m+1)) A.B.a (m+1) (windward Ξ R S p N n (m+1)) (upfront (A.B.a.clock.hatBeta (m+1)) p ε))
include hΞ hE he hq hΦ hv hε hp hm Gq
lemma terrific : K=A' ∧ Inland Ξ R (Y) Orchard.beam0 Z p (u) ∧ Affords K τ m Ū u:= by
   have hx:K=A':= ponds S N n m (rose0 S) hm
   have hl:= King.leaseArg Ξ R Y σ (σ).property Z p hE he hΞ hm hΦ hp Gq g hq ε hv
   have he₀:= (Reel.trust R he p hΦ hp).2.2 ε hε
   have hz:= Reel.ipos (τ) m p ε; have hY:= Reel.ipos (τ) (m+1) p ε
   have hy : h (m+1)^requested (p+1) ε + u₀/8 ≤ u:=by
      unfold upfront at *; linarith only [hY,he₀.2] -- unfold at * maybe wrong notation
   have hU:= Inland.raise Ξ R S p hm hl hy
   refine ⟨hx,hU,?_⟩
   rw [winding Ξ R S p hm,hx]; apply Reel.orient hz (le_refl (u)) ?_ hU.stakes; linarith only [he₀.1,hz]
omit hm hΦ hv Gq hΞ hE hq in
lemma root_at (hV: p ≤ A.B.a.clock.J (N+1)):
   Affords (S.realBeat 0 N n N) τ N (windward Ξ R S p N n N) (upfront (A.B.a.clock.hatBeta N) p ε):=by
   rw [King.attop]
   let W:=S.realBeat 0 N n N; have hh:= (Reel.trust R he p hV hp).2.2 ε hε
   refine ⟨Reel.ipos (τ) N p ε,by linarith only [hh.1,Reel.ipos τ N p ε],fun i=>?_⟩
   unfold Reel.curve; rw [sub_self,smul_zero,smul_zero,add_zero,bend]; exact ((S.ticking N n (Uses.centerP _)).prices N (Nat.zero_le _) le_rfl).1.valid
omit hm hΦ hv Gq in
lemma tunnels (k:ℕ)(hX:∀ m≥k,p≤ A.B.a.clock.J (m+1) ∧ 3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε) (hh:k ≤ m)(hk:m≤N) : Affords K τ m Ū u:= by
   suffices heq : ∀ s:ℕ, ∀ m, N-m=s → k ≤ m → m≤N → Affords (S.realBeat 0 N n m) (A.B.a) m (windward Ξ R S p N n m) (upfront (A.B.a.clock.hatBeta m) p ε) by exact heq _ m rfl hh hk
   intro s; induction s with
   | zero => intro m hv hh hk; have hy:m=N:=by omega
             subst m; exact root_at Ξ R he S p hp ε hε ((hX N hh).1)
   | succ s ih=> intro m hv hh hk; exact (terrific Ξ R hE hΞ he hq S p hp ε hε (m:=m) (N:=N) (by omega) (hX m hh|>.1) (hX m hh|>.2) (ih (m+1) (by omega) (by omega) (by omega))).2.2
omit Gq hΦ hv hm in
/-- Actual every-policy dereferenced. All previously published costs apply simultaneously
    since using `Uses`, not pricing a different copy that meets merely the same tilt. -/
lemma elastic (k:ℕ)(hX:∀ i≥k,p≤ A.B.a.clock.J (i+1) ∧ 3*CalendarStep.loss (A.B.a.clock.J (i+1)) ≤ ε) (hh:k ≤ m) (hx:m≤N) :
    Affords K τ m Ū u ∧ ∀ hm:m<N, let X:= Marker.beam R S (n:=n) hm; K=X.result σ ∧ Inland Ξ R X Orchard.beam0 Z p (u):= by
   refine ⟨tunnels Ξ R hE hΞ he hq S p hp ε hε _ hX hh hx,fun hm=>?_⟩
   have hM:= terrific Ξ R hE hΞ he hq S p hp ε hε hm (n:=n) (hX m hh).1 (hX m hh).2 (tunnels Ξ R hE hΞ he hq S p hp ε hε _ hX (hh.trans (Nat.le_add_right ..)) hm)
   exact ⟨hM.1,hM.2.1⟩
end YM.LocalTaylorR2.King
