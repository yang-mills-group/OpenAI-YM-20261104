import YM.Integration.WilsonConditionalTaylorUntunedLog
import YM.MSbar.Ballet.Visor

/-! At every physical step the signed unretuned *vacuum* is independent
of the chosen forest and legal offset. Both Taylor expansions predict
the same measured shunt at all real fields, before changing the coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorUnresetForest

open Function Filter Set Finset PowerSeries Lattice RG Wilson Tree Exterior Precision Push.Uniform
open MSbar MSbar.Midpoint MSbar.Wave MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open PertExtension.Series PertExtension.Series.Tested PhysicalNext.Repeat.Legato
open WilsonConditionalTaylorSceneCalibration WilsonConditionalTaylorSceneChoices
open scoped Classical Topology BigOperators

variable {G : Gauge} {c : Side} {T : ℝ → Config G c → ℝ} {P : PathData G} {p : Clip} {r : ℕ}

theorem identifies {A B : Nesting G c} (one : Trend T A P p r) (two : Trend T B P p r) :
    FormalBulk08.Series.Through r A B := by
  intro i paid
  apply MvPolynomial.funext
  intro x
  let film:=fun g=>Real.log (T g (postcard G c g x))+height c p P x
  have regular : ∀ᶠ g in Tested.germ, yard 1 g x :=
    (awake.eventually_ge_atTop ‖x‖).mono fun _ h=>by simpa [yard] using h
  have price (U : Nesting G c) (fit : Trend T U P p r) :
      Wave.Grade (fun g=>film g-taste r (picture x U) g) (r+1) :=
    Rolling.Price.inherits (V:=fun _ (_:Unit)=>True) (fit.tune 1) (fun _ _=>x) (regular.mono fun _ h _ _=>h)
  apply sub_eq_zero.mp
  apply Wave.magnitude (n:=r) (f:=fun j=>MvPolynomial.eval x (coeff j A)-MvPolynomial.eval x (coeff j B)) _ i paid
  apply ((price B two).cut (price A one)).egress
  filter_upwards with g _ _
  simp only [taste,picture,PowerSeries.coeff_map,mul_sub,Finset.sum_sub_distrib]
  ring

variable (R : Run G) {N n k : ℕ} {S : Scene R.family.path.levels n r} {v : G.Color}
    (scene : Realized R.alloy.B.kin N n k r v S) (j : ℕ) (lo : k≤j) (hi : j<N)

def bank (R : Run G) {N j n r : ℕ} (S : Scene R.family.path.levels n r)
    (F : Forest (R.family.path.levels.clock.op j n).ratio) (t : (R.family.path.levels.clock.op j n).Choices) :=
  colorCut F t (R.alloy.B.kin.path N (j+1)) (R.family.path.levels.params (j+1)).clip R.metals.O
    (S.Poly (j+1)) (R.alloy.B.kin.stationary N j n F)

include scene lo hi in
theorem physical (F : Forest (R.family.path.levels.clock.op j n).ratio) (t : (R.family.path.levels.clock.op j n).Choices) :
    Trend (shunt (R.family.path.levels.clock.op j n) (S.film (j+1))) (bank (N:=N) R S F t)
      (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip r := by
  let K:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  let X:=R.alloy.B.kin.path N (j+1)
  let Y:=R.alloy.B.kin.path N j
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have suitable:=(townsR R.b R.Q R.T R.t R.stories R.doors ch).towns j n
  have serves:Serves (R.family.path.levels.clock.op j n) G:=⟨suitable.1,(R.alloy.B.a.blocks ..).symmetric,
    (R.alloy.B.a.blocks ..).gauge,suitable⟩
  have fit:=(scene.budget (j+1) hi (lo.trans (Nat.le_succ j))).1
  have pos : Matrix.PosDef (Push.Uniform.block (priced F t H'.clip X) 0) :=
    blueprint F t X H'.clip suitable.1 fit.quiet (K.post.price _) (K.planned.gap N j n hi F)
  exact newT F t X Y H'.clip H.clip (R.alloy.B.kin.stationary N j n F) R.metals.O R.alloy.B.ratio
    (S.Poly (j+1)) (S.film (j+1)) r serves (K.planned.critical N j n hi F).1
    (K.planned.classicalPart N j n hi F) fit pos

include scene lo hi in
theorem every (F F' : Forest (R.family.path.levels.clock.op j n).ratio)
    (t t' : (R.family.path.levels.clock.op j n).Choices) :
    FormalBulk08.Series.Through r (bank (N:=N) R S F t) (bank (N:=N) R S F' t') :=
  identifies (physical R scene j lo hi F t) (physical R scene j lo hi F' t')

theorem actual {u : G.ColorIndex} (source : Realized R.alloy.B.kin N n k r (Lis.sun G u) S)
    (F : Forest (R.family.path.levels.clock.op j n).ratio) (t : (R.family.path.levels.clock.op j n).Choices) :
    FormalBulk08.Series.Through r (untuned R source j lo hi) (bank (N:=N) R S F t) :=
  every R source j lo hi _ F _ t

end YM.Integration.WilsonConditionalTaylorUnresetForest
end

