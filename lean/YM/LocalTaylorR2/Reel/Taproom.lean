import YM.LocalTaylorR2.Reel.Harmony
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
open Marlin Capstone Ovens Progress.DirectedRecipe
section general
variable (J:Listing G c)(q:ℕ)
-- the inflation inserts the beacons strut. Stage. tags not changed
variable {e:ℝ} {Φ x y:Scroll G c} {B:BudgetPoint} {U V:Collection.Source G c}
lemma biszero (w:ℕ)(t: Trio.Offer G c) (he:Meadow.Budget B J.reg U.logRead e) : Meadow.Budget B (lodge J q w).reg (bison U 0 t).regular e:=by
  have hh: Meadow.Budget B (leap q) (G:=G) (0: Trio.Offer G c) 0:= ⟨fun _=>0,fun i=>by simp [SumBudget],fun i=> ⟨CouplingShape.reg_const (p:=B) (G:=G) 0,no_cost ..⟩⟩
  simpa only [mul_zero,add_zero] using reg_bison J q w U 0 t he hh
lemma lanes {A Y Z:Trio.Offer G c} (he: Meadow.Budget B J.reg (U.logRead-V.logRead) e): Meadow.Budget B (lodge J n q).reg ((bison U A Y).regular - (bison V A Z).regular) e:=by
  have h (X:Trio.Offer G c) : (bison V A Z).regular=(bison V A X).regular:= rfl
  let T:= ({V with logRead:=U.logRead-V.logRead}:Collection.Source G c)
  rw [show (bison U A Y).regular=_ from Capstone.layout_add (X:=U) (Y:=V) (Z:=T) A A 0 Y (add_zero _).symm (show U.logRead= V.logRead + (U.logRead-V.logRead) by abel), h Y,add_sub_cancel_left]; exact biszero J n q Y (show Meadow.Budget B J.reg T.logRead e from he)
end general
section glazing
variable (Z : Collection.Listing G c)(c' w:ℕ)(p:BudgetPoint)(χ:Chi)
def Yoke (x:Scroll G c) : Prop := ∃ (g:Magazine H→ Config G c→ℝ)(u:Trio.Offer G c), x = (bison ⟨ choir g ∘ pennant H, 0⟩ u 0).regular
lemma replenished {α X:Trio.Offer G c}{Φ:Scroll G c}{uV:Collection.Source G c}(h:∃ g, uV.logRead=choir g ∘ pennant H)(hp:Φ=(bison uV α X).regular): Yoke H Φ:=by
  obtain ⟨g,h⟩:= h; rw [hp]; exact ⟨g,α,by unfold bison; dsimp only []; rw [h]⟩
variable {a b: Scroll G c}{p}
lemma active_sub (hx:Yoke H a)(hy:Yoke H b): Yoke H (a-b):=by
    obtain ⟨g,X,rfl⟩:=hx; obtain ⟨k,Y,rfl⟩:=hy; refine ⟨g-k,X-Y,?_⟩
    funext i T; unfold bison; simp only [Function.comp_apply,Pi.sub_apply]; rcases _ : leanU c i with i|i <;> simp [choir] <;> ring
lemma active_scale (hx:Yoke H a)(t:ℝ):Yoke H (t • a):=by
    obtain ⟨g,Y,rfl⟩:=hx; refine ⟨t • g, t • Y,?_⟩; funext i T; unfold bison; simp only [Function.comp_apply,Pi.smul_apply]; rcases _ : leanU c i with i|i <;> simp [choir] <;> ring
variable (p)
lemma scoop {e b κ:ℝ}{X Y:Collection.Source G c} (hx : Collection.Local (pluck p (lodge (Beam.marquee H p) c' w)) p X e κ)(he:Y.hardRead=X.hardRead)(hv:Yoke H Y.logRead)(hy:Meadow.Budget p (lodge (Beam.marquee H p) c' w).reg Y.logRead b): Collection.Local (pluck p (lodge (Beam.marquee H p) c' w)) p Y b κ:= by
    obtain ⟨g,U,hg⟩:=hv; let f:= Beam.marquee H p; let z:Alliance H H 1 0:=Match.staple rfl rfl rfl
    let X':={ (plusone H z Chi.canonical 0) with logRead:= choir g ∘ pennant H }
    refine Capstone.mounted hx he ⟨lodge f c' w, bison X' U 0, rfl,hg.symm,fun s q=>?_⟩ hy
    exact Marlin.reeds f c' w _ _ _ _ _ ((Beam.moves H p Chi.canonical z s q g).some)
end glazing
end YM.LocalTaylorR2.Reel
