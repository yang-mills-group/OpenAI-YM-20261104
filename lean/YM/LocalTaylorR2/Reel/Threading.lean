import YM.LocalTaylorR2.Reel.Loor
import YM.LocalTaylorR2.Marker.Pad
/-! # actual `Uses` from Career. Campaign: every-order-in-interaction iteration of full **local E-data**, not of correlations. Holds actual K and parameters fixed channel, budgets every step. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
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
open Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
variable {G:Gauge}
section arithmetic
lemma orient {V:Levels G}{m:ℕ}{b:Side}{U:Rep G b} {E:Scroll G b}{d e:ℝ}
    (he:0<d) (hx:e≤d) (hh:2*d≤ V.clock.allowance m)(h: ∀ g:ℝ,Sizing V m (bend U (U.activities.E+g • (E-U.activities.E))) (Time.fraction V m+|g| * e)):
    Affords U V m E d := by
     refine ⟨he,hh,fun i=>?_⟩; unfold Reel.curve; rw [smul_smul]
     apply book_up (h _); unfold Time.fraction
     let C:=V.clock.allowance m; let g:=(i:ℝ); have hg: |g| ≤1:= by exact abs_le.mpr i.property
     have hC: 0 ≤ C:= (mul_pos zero_lt_two he).le.trans hh; let a:=C/(2*d); have ha:0≤a:=by unfold a; positivity
     suffices hz : |g*a| * e ≤ C/2 by change C/32 + |g*a| * e ≤ C; linarith only [hC,hz] -- unfold
     calc
      _ ≤ a * d:= by rw [abs_mul,abs_of_nonneg ha]; exact (mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg _) ha)).trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ha hg) he.le)
      _ = C/2 := by unfold a; field_simp
lemma ipos (V:Levels G)(m p:ℕ)(ε:ℝ):0<upfront (V.clock.hatBeta m) p ε:=mul_pos zero_lt_two (Real.rpow_pos_of_pos (zero_lt_one.trans (V.fits.delayed _)) _)
end arithmetic
variable {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m N n:ℕ} (R:Factor A) (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hq:Mallow.RG12.Earned (checkD G) R.shape A.delay)  {g:G.Simple} (S:Uses R g)
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
def descend (N n:ℕ) (m:ℕ): Reel.Scroll G (A.B.a.S.side m n):= if hm:m<N then
    sauce R (Marker.beam R S (n:=n) hm) Orchard.beam0 (descend N n (m+1)) p else (S.realBeat 0 N n m).activities.E
termination_by N - m
local notation "Ū" => descend R S p N n m
local notation "Z" => descend R S p N n (m+1)
local notation "A'"=> (Y).result σ
lemma descent : (Ū)=sauce R Y σ Z p:=by rw [descend,dif_pos hm]
lemma attop : descend R S p N n N=(S.realBeat 0 N n N).activities.E:=by rw [descend,dif_neg (lt_irrefl _)]
local notation "v" => A.B.a.clock.allowance m
local notation "Φ"=> (A.B.a.clock.J (m+1))
variable (hΦ:p ≤ A.B.a.clock.J (m+1)) (hv:3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε)
lemma Award.raise {w:Scroll G (A.B.a.S.side (m+1) n)} {x y:ℝ} (H:Award R (Marker.beam R S hm) Orchard.beam0 w p x) (hx:x≤y) : Award R (Marker.beam R S hm) Orchard.beam0 w p y:= ⟨⟨book_up H.estate.1 hx, book_up H.estate.2 (add_le_add_right hx _)⟩,fun c=>book_up (H.stakes c) (add_le_add_right (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) _),H.price,H.rooms,H.scalar.trans hx,H.beta.trans hx⟩
variable (Gq:Affords (S.realBeat 0 N n (m+1)) A.B.a (m+1) (descend R S p N n (m+1)) (upfront (A.B.a.clock.hatBeta (m+1)) p ε))
include hE he hq hΦ hv hε hp hm Gq
lemma fortuitous : K=A' ∧ Award R (Y) Orchard.beam0 Z p (u) ∧ Affords K τ m Ū u:= by
   have hx:K=A':= ponds S N n m (rose0 S) hm
   have hl:= Reel.ordained R Y σ (σ).property Z p hE he hm hΦ hp Gq g hq ε hv
   have he₀:= (Reel.trust R he p hΦ hp).2.2 ε hε
   have hz:= Reel.ipos (τ) m p ε; have hY:= Reel.ipos (τ) (m+1) p ε
   have hy : h (m+1)^requested (p+1) ε + u₀/8 ≤ u:=by
      unfold upfront at *; linarith only [hY,he₀.2] -- unfold at * maybe wrong notation
   have hU:= Award.raise R S p hm hl hy
   refine ⟨hx,hU,?_⟩
   rw [descent R S p hm,hx]; apply Reel.orient hz (le_refl (u)) ?_ hU.stakes; linarith only [he₀.1,hz]
omit hm hΦ hv Gq hE hq in
lemma root_at (hV: p ≤ A.B.a.clock.J (N+1)):
   Affords (S.realBeat 0 N n N) τ N (descend R S p N n N) (upfront (A.B.a.clock.hatBeta N) p ε):=by
   rw [Reel.attop]
   let W:=S.realBeat 0 N n N; have hh:= (Reel.trust R he p hV hp).2.2 ε hε
   refine ⟨Reel.ipos (τ) N p ε,by linarith only [hh.1,Reel.ipos τ N p ε],fun i=>?_⟩
   unfold Reel.curve; rw [sub_self,smul_zero,smul_zero,add_zero,bend]; exact ((S.ticking N n (Uses.centerP _)).prices N (Nat.zero_le _) le_rfl).1.valid
omit hm hΦ hv Gq in
lemma iterated (k:ℕ)(hX:∀ m≥k,p≤ A.B.a.clock.J (m+1) ∧ 3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε) (hh:k ≤ m)(hk:m≤N) : Affords K τ m Ū u:= by
   suffices heq : ∀ s:ℕ, ∀ m, N-m=s → k ≤ m → m≤N → Affords (S.realBeat 0 N n m) (A.B.a) m (descend R S p N n m) (upfront (A.B.a.clock.hatBeta m) p ε) by exact heq _ m rfl hh hk
   intro s; induction s with
   | zero => intro m hv hh hk; have hy:m=N:=by omega
             subst m; exact root_at R he S p hp ε hε ((hX N hh).1)
   | succ s ih=> intro m hv hh hk; exact (fortuitous R hE he hq S p hp ε hε (m:=m) (N:=N) (by omega) (hX m hh|>.1) (hX m hh|>.2) (ih (m+1) (by omega) (by omega) (by omega))).2.2
omit Gq hΦ hv hm in
/-- Actual every-policy dereferenced. All previously published costs apply simultaneously
    since using `Uses`, not pricing a different copy that meets merely the same tilt. -/
lemma plausible (k:ℕ)(hX:∀ i≥k,p≤ A.B.a.clock.J (i+1) ∧ 3*CalendarStep.loss (A.B.a.clock.J (i+1)) ≤ ε) (hh:k ≤ m) (hx:m≤N) :
    Affords K τ m Ū u ∧ ∀ hm:m<N, let X:= Marker.beam R S (n:=n) hm; K=X.result σ ∧ Award R X Orchard.beam0 Z p (u):= by
   refine ⟨iterated R hE he hq S p hp ε hε _ hX hh hx,fun hm=>?_⟩
   have hM:= fortuitous R hE he hq S p hp ε hε hm (n:=n) (hX m hh).1 (hX m hh).2 (iterated R hE he hq S p hp ε hε _ hX (hh.trans (Nat.le_add_right ..)) hm)
   exact ⟨hM.1,hM.2.1⟩
end YM.LocalTaylorR2.Reel
