import YM.LocalTaylorR2.Reel.Prod
/-! # Strict consumer course living price: all periodic campaign steps along re-expression -/
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
open Pert.Asymptotics Orbit
set_option quotPrecheck false
variable {C:Family G}{g:G.Simple}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (harvest Δ))
open Extra.Histories Planned.GuardedAtom Guard
lemma syllable {n:Side}{t:Levels G}{i:ℕ}{U X:Rep G n}{f z:Scroll G n}{a b c d :ℝ} (hX:U=X)(h: f=z)
    (hb:Affords U t i f d) (ht: d≤a)(hp:U.p=t.budget i)
    (he: HasSlots (t.budget i) (bend X z).activities) (hf: HasSlots (t.budget i) (bend X (X.activities.E-z)).activities)
    (hA: X.eval=(bend X z).eval*(fun U'=>Real.exp (-((bend X (X.activities.E-z)).activities.additive (t.budget i) U'))))
    (hF: Sizing t i (bend X (X.activities.E-z)) d)
    (hg:(t.budget i).threshold^2 * |X.beta-b| ≤ d) (hh:|X.v-c| ≤ d):
    let V:= t.budget i; let T:= (bend U (U.activities.E-f)); let R:=bend U f; let W:= t.clock.forcedAllowance i
    HasSlots V R.activities ∧ HasSlots V T.activities ∧ U.eval=R.eval*(fun U'=>Real.exp (-(T.activities.additive V U'))) ∧ U.activities.K= R.activities.K ∧ T.activities.K=U.activities.K ∧ R.activities.Valid V (t.clock.allowance i) W ∧ T.activities.Valid V a W ∧ V.threshold^2 * |U.beta-b| ≤ a ∧ |U.v-c| ≤ a:=by
    subst X; subst z; intro V T R W; obtain ⟨s,-,-,hy⟩:= blend_it hb; have hR:=hb.stamps s; rw [hy] at hR; exact ⟨he,hf,hA,rfl,rfl,Eq.mp (congr_arg (R.activities.Valid · _ W) hp) hR.labels, Eq.mp (congr_arg (T.activities.Valid · a W) hp) (book_up hF ht).labels,hg.trans ht,hh.trans ht⟩
lemma walk (he:Semester U) (p g':ℕ)(hx:3≤p) (ε:ℝ)(hq:0<ε)(hε:ε≤1): ∀ᶠ m:ℕ in atTop, ∀ i≥m,
    let a:= U.cost.B.a; let t:= a.budget i; let S:=U.uses; let g m :=upfront (a.clock.hatBeta m) p ε; g'≤ t.order ∧ ∀ (N n:ℕ) (hm:i<N),
      let H:= Marker.beam U.factor S (n:=n) hm; let I:=S.realBeat 0 N n i; let f:=t.threshold; let v:=a.clock.forcedAllowance i
      let f':=descend U.factor S p N n i; let r:=descend U.factor S p N n (i+1); let y:= bend I f'; let x:=bend I (I.activities.E-f')
      let u:= Pert.Asymptotics.regulatorRun C N n i; let B:=2*(Real.sqrt 2*u)^((p+1:ℝ)-ε)
      Affords (S.realBeat 0 N n (i+1)) a (i+1) r (g (i+1)) ∧
      I.p=t ∧ I.activities.E-y.activities.E=x.activities.E ∧ HasSlots t y.activities ∧ HasSlots t x.activities ∧
      I.eval=y.eval*(fun U'=>Real.exp (-(x.activities.additive t U'))) ∧ I.activities.K= y.activities.K ∧ x.activities.K=I.activities.K∧ y.activities.Valid t (a.clock.allowance i) v ∧ x.activities.Valid t B v ∧
      f^2 * |I.beta-βGuess U.factor H Orchard.beam0 r p| ≤ B ∧ |I.v-priceGuess U.factor H Orchard.beam0 r p| ≤ B:= by
   filter_upwards [he.semester p g' hx ε hq hε] with m hM; intro i hi a t S g'; let k:=a.clock.J i
   refine ⟨(hM i hi).1,?_⟩; intro N n hm H I f v f' r y x u B
   have h₀ := hM i hi|>.2.2 N n hm.le; have h₁ := hM (i+1) (hi.trans (Nat.le_succ i)) |>.2.2 N n hm
   obtain ⟨hg,Hh⟩:= h₀.2.2.2 hm; let V:= H.result Orchard.beam0; have hl:I=V:=hg
   have hb:HasSlots t V.activities:=slots0 S N i n (rose0 S) hm
   have he:f'=sauce U.factor H Orchard.beam0 r p:=Reel.descent U.factor S p hm
   let d₀:=upfront (a.clock.hatBeta i) p ε
   have hT : I.p=t:= ((S.ticking N n (Uses.centerP _)).prices i (Nat.zero_le _) hm.le).1.point
   have hq : d₀ ≤ B:= mul_le_mul_of_nonneg_left h₀.2.2.1 zero_le_two
   refine ⟨h₁.1,hT,rfl,syllable hl he h₀.1 hq hT (Hh.rooms hb).2 (Hh.rooms hb).1 Hh.price Hh.estate.1 Hh.beta Hh.scalar⟩
end YM.LocalTaylorR2.Reel
