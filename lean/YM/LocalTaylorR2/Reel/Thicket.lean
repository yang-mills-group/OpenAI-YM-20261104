import YM.LocalTaylorR2.Render
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Fluent
/-! # Substitute E only in *same* H-homographic picture. No extra recourse.
  The functions here freeze semantics of χ,T,Q and R (through β etc.) but
  simply **override** E field *at each actual address*. Price must still include
  all α and K, not display unflagged-only Push. This image is usable even without
  a constructed G2/Calendar for the proposed E.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle
abbrev Scroll (G:Gauge)(n: Side) := ℕ → Config G n → ℝ
def bend {G:Gauge}{n:Side}(R:Rep G n)(ψ : Scroll G n): Rep G n:={R with activities:= {R.activities with E:= ψ}}
lemma plain (R:Rep G f): bend R R.activities.E=R:=rfl
lemma admissible (J:Cash W s μ L Q o C T R') (hp:R.path=R'.path)(hv:R.activities.reg=R'.activities.reg)(hx:R.activities.forced=R'.activities.forced)(p:H.ThinP)(q:J.ThinP)(hq:q.val=p.val) : Candle.live H p ↔ Candle.live J q:= by
  unfold Candle.live Candle.vetted; rw [hq,same_area (H:=H) (J:=J) hp hv hx]
  unfold troupe Contract.sealed Contract.incidence; rw [hx]
lemma pasture (J:Cash W s μ L Q o C T R') (hp:R.path=R'.path)(hv:R.activities.reg=R'.activities.reg)(hx:R.activities.forced=R'.activities.forced)(p:Molecule S) (f:Port.Test T): episode H χ p f=episode J χ p f:=by
  ext x
  unfold episode Cash.unionP; rw [same_area (H:=H) (J:=J) hp hv hx]
open Polar
variable (E : Reel.Scroll G f)
def sprout (_H : Cash W s μ L Q o C T R) (E: Reel.Scroll G f) (i:LogIndex c f): Port.Test T:= fun _ X z=> Polar.logMoment X o.a (bend R E) Q.table (Vine.worldZ X R.beta z) (X.input (Vine.worldZ X R.beta z)) z i
def press {p:Molecule S}{l:ℕ}(q:Paint p l):Port.Test T:= fun F X w=> ∏ i : ↥(logs p), Series.split (q i) (sprout H E i.val F X w)
-- version truncated book never evaluates any residual at new E
def team {l:ℕ} : Expansions H l:=fun p q V=> if live H p then convolve (U:=p.val) q (fun i=> episode H χ p.val (press H E i) V) else 0
lemma sown (_J : Cash W s μ L Q o C T (bend R E))(i:LogIndex c f): weightLog _J i=sprout H E i:=rfl
lemma capped {p:Molecule S}{l:ℕ}(_J : Cash W s μ L Q o C T (bend R E))(q:Paint p l): letters _J q=press H E q:=rfl
lemma uniformly {l:ℕ} (J:Cash W s μ L Q o C T (bend R E))(p:H.ThinP)(q:Orders l)
    (Y:J.ThinP)(h:Y.val=p.val)(hq:q.val ≤ l): team H (χ:=χ) E p q = Candle.sprig J χ Y q:=by
  have hu : q≠ Candle.perch l:=fun he=> by rw [he, Candle.perch] at hq; rw [Fin.val_last] at hq; omega
  funext z; rw [Candle.sprig,if_neg hu]; unfold team Candle.script
  rw [← admissible H J rfl rfl rfl _ _ h]
  split
  · generalize_proofs
    rw [h]; apply congr_arg; funext i; exact congr_fun (pasture H J rfl rfl rfl p.val (letters J i)) z
  rfl
variable {I₁:Cash W s μ L Q o C T R'} (X: Alliance I₁ H 1 0)
lemma provision {l : ℕ} (J:Cash W s μ L Q o C T (bend R E))(u:Alliance H J 1 0)(hu:u.units=Equiv.refl _)
    (Z: H.fragrances)(V: Config G c)(F:ℕ → Prop)(hF:∀ i, F i→ i≤l): fullSegments (fun _ i=>F i) (team H E (l:=l) (χ:=χ)) Z V= fullSegments (fun _ i=>F i) (Candle.sprig J χ (l:=l)) (u.furrow Z) V:= by
  unfold fullSegments; rw [Match.weighs u.bearing u.sec Z]; congr 1
  apply Finset.sum_congr rfl; intro i hi; unfold aliquot
  apply prod_congr rfl; intro q hq; apply congr_fun; apply uniformly H E J (Z.2 q)
  · change u.units _=_; rw [hu]; rfl
  exact (le_trans (single_le_sum (f:=fun j=> (i j).val) (fun _ _=>Nat.zero_le _) (mem_univ q)) (hF _ (mem_filter.mp hi).2))
def crawl (χ : Chi) (γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop): Magazine I₁ → Config G c→ℝ:= Sum.elim
      (fun i=> (-1:ℝ) • fullSegments (M:=p) (fun _ q => f q) (team H E (χ:=χ)) (X.furrow i))
      (fun (i : Songbook c)=> (if φ then (1:ℝ) else 0) • opus I₁ X χ γ (Sum.inr i))
def sight (χ : Chi) (γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop):= choir (crawl H E X χ γ p φ f) ∘ pennant I₁

lemma garbey {l:ℕ} (p:ℕ→Prop)(χ:Chi)(γ:ℝ)(Rz:Bool){I₂:Rep G f} (I':Cash W s μ L Q o C T I₂) (T:Alliance I₁ I' 1 0)(x:Expansions I' l)(hk:R.beta=I₂.beta)
   (hh:∀ i:I₁.fragrances,fullSegments (fun _ j=>p j) (team H E (l:=l) (χ:=χ)) (X.furrow i)=fullSegments (fun _ j=>p j) x (T.furrow i)):
    sight H E X χ γ l Rz p=(cohort I' (χ:=χ) T γ x Rz p).logRead:=by
    dsimp only [sight,crawl,cohort,opus,Sum.elim_inr]; simp_rw [hh,hk]
lemma verges (J:Cash W s μ L Q o C T (bend R E))(T:Alliance I₁ J 1 0)(ht:T.units=Equiv.refl _)(hx:X.units=Equiv.refl _)(χ:Chi)(γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop)(he:∀ i,f i→ i ≤ p): sight H E X χ γ p φ f=(cohort J («χ»:=χ) T γ (Candle.sprig J χ) (M:=p) φ f).logRead:= by
   apply garbey H E X _ _ _ _ J T _ rfl
   intro i; funext V; let L:Alliance H J 1 0:= Match.staple rfl rfl rfl
   rw [← Yearling.trappings X L T hx rfl ht i]; exact provision H E J L rfl (X.furrow i) V f he
lemma accrues (χ:Chi)(γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop)(he:∀ i,f i→ i ≤ p):
   sight H R.activities.E X χ γ p φ f=(cohort H («χ»:=χ) X γ (Candle.sprig H χ) (M:=p) φ f).logRead:= by
   apply garbey H R.activities.E X _ _ _ _ H _ _ rfl
   intro i; funext V; let u:Alliance H H 1 0:=Match.staple rfl rfl rfl
   have h (z:H.fragrances): u.furrow z=z:= by rcases z with ⟨i,f⟩; rfl
   have hw:= provision H R.activities.E H u rfl (χ:=χ) (X.furrow i) V f he; exact hw.trans (congr_arg (fun y: H.fragrances=> fullSegments (fun _ j=>f j) (sprig H χ (l:=p)) y V) (h (X.furrow i)))
end YM.LocalTaylorR2.Reel
