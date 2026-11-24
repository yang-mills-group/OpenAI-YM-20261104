import YM.RegulatorIR.Binding.Pills
import YM.RegulatorIR.Binding.Chamber

/-! Abstract one-step square completion and primitive-jets comparison
interfaces. Inputs are layer/germ facts (need further geometrical and
coefficient proofs for actual application). Derive the comparison through
different weights and powers t. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge} {E I J L X Y Z:Type}[Fintype E][Fintype I][Fintype J][Fintype L][Fintype X][Fintype Y][Fintype Z]
variable {m:ℕ}

-- L integrator, X joint slot alphabet, Y inlet alphabet, Z outlet.
structure Medium (G:Gauge)(I Y:Type) where
  color : Meadow G I → Y→ℝ
  kinetic : Meadow G I→ℝ
  -- optionally exact Q. not a bonus amplitude

def manuscript (F A:Hook G E I)(w:Meadow G I):ℝ⟦X⟧:= PowerSeries.mk (tomorrow F A w)

-- Gaussian quadratic binding. drag samples legs actually assembled in passing to coarse. Can support injection if at last Z no indices. Cov matrix support inferred. Triangulation amplitude.
structure Clip {G:Gauge}{I J L: Type}{V:Transfer I L G}{F:Hook G L J}
     (S: Medium G I Y)(C: Medium G J Z)(a:Y↪X)(b:Z↪X)(A B: Layer X X) (U:Orders X)[Fintype L][Fintype I][Fintype J] where
 law : Law (Meadow G L)
 slide : Meadow G J→ Meadow G L
 directions : X→Module.Dual ℝ (Meadow G L)
 covariance : Diagram.Gaussian.bond law directions=A
 -- for all shifted integrators. B deterministic poles. can use Y-output with no evaluation on values at origin terminal.
 witness : ∀ w x v, S.color (V.curve (x+slide w)) v= announce B (dilute b (C.color w)) (a v)+ directions (a v) x
 gap w x : S.kinetic (V.curve (x+slide w))+Series.Radial.jet (priceMap F) 2 (x+slide w,1,w) = C.kinetic w+ law.P x x/2
 sing w x :
   let d:=announce B (dilute b (C.color w)); let y:=x+slide w
   PowerSeries.mk (fun i=> normTerm (aura (1:Hook G L J)) (priceMap F) i (y,1,w))= PowerSeries.C (jacobian (tray G) (0:Meadow G L) * Real.exp (-jet (priceMap F) 2 (y,1,w))) * expo (flavor 2 (d+fun i=> directions i x) U)
 symmetry : gradedSymmetric U
 order : Vacuum U
-- args implicit order classes infer

variable {T:Viewport G I}{Q:Viewport G J}{W:Transfer I L G}{F M:Hook G E I}
  {R:Hook G L J} {H:L} {s:ℕ}{P:Medium G I Y}{N:Medium G J Z}{a:Y↪X}{b:Z↪X}{A B:Layer X X}{U:Orders X}

lemma acct {L: Type} [Fintype L] (D:Law (Meadow G L)): Integrable D.kern (tangent G L):= by
 have hh:= D.integrable_entry (tangent G L) (A:=1) (Zone.Invoice.const (1:ℝ)) continuous_const; rwa [one_mul] at hh

def sizes (D:Law (Meadow G L)):= ∫ x,D.kern x ∂tangent G L
lemma sizes_pos (D:Law (Meadow G L)):0<sizes D:= MeasureTheory.integral_exp_pos (acct D)
-- Fee scalar J

def morning (G:Gauge) (L:Type)[Fintype L]:= Chart.jacobian (Orb.tray G) (0:Meadow G L)
lemma dawn (G:Gauge)(L:Type)[Fintype L]: 0<morning G L:=by
 apply Finset.prod_pos; intro i _; exact lt_max_of_lt_left (show 0 < (tray G).scale*(tray G).J 0 by rw [(traySpec G).anchored,mul_one];exact (traySpec G).scale)

namespace Clip
variable (C:Clip (V:=W) (F:=R) P N a b A B U)
omit [Fintype Y][Fintype Z] in
lemma conjunction (w x) (y) : (announce B (dilute b (N.color w))+ fun i=> C.directions i x) (a y)=P.color (W.curve (x+C.slide w)) y := (C.witness w x y).symm
omit [Fintype Z] in
lemma offerP (D:Orders Y)(u:ℕ)(w x) : flavor u (P.color (W.curve (x+C.slide w))) D= flavor u (announce B (dilute b (N.color w))+fun i=> C.directions i x) (Cluster.present a D):= by rw [flavor_offer, show _ ∘ _= _ from funext (C.conjunction w x)]
end Clip

-- unnormalized accounting statement with displayed kinetic Q before chart Haar.
structure Dusk (s:ℕ)(V:Hook G E I)(F:Hook G E I)(P:Medium G I Y)(T:Orders Y)(ξ:ℝ⟦X⟧)(Q:Orders Y)(m:ℕ) : Prop where
 bare w : manuscript V 1 w = PowerSeries.C (Real.exp (-P.kinetic w)) * ξ * Formal.expo (flavor 2 (P.color w) T)
 stamped w : manuscript V F w = manuscript V 1 w * PowerSeries.X^s * flavor m (P.color w) Q
  -- T positive; F input divided by common Laurent
 awake : 0 < PowerSeries.coeff 0 ξ
 vacuum : Vacuum T
 faces : gradedSymmetric T
 since : ∀ e,Within (e+m) (Q e)
 goals : gradedSymmetric Q

def supply (T:Orders Y)(a:Y↪X)(U:Orders X):= Cluster.present a T + U
lemma order_supply {T:Orders Y}(h:Vacuum T) (hx:Vacuum U): Vacuum (supply T a U):=by
 intro k e he; change Cluster.present a T k e+U k e≠0 at he
 by_cases hv:U k e=0
 · rw [hv,add_zero] at he; exact h k e (fun h'=> he (by unfold Cluster.present; rw [h']; ext1 u; simp [offer,Stalk.collect]))
 exact hx k e hv
omit [Fintype X][Fintype Y] in
lemma sort_supply {T:Orders Y} (h:gradedSymmetric T)(hh:gradedSymmetric U): gradedSymmetric (supply T a U):= fun i j=> symmetric_add (Cluster.sym_offer a T h i j) (hh i j)
omit [Fintype X] in
lemma vacuum_lo (T:Orders X)(h:Vacuum T): T 0=0:= funext (fun _=>Classical.byContradiction (fun hv=> lt_irrefl 0 (h _ _ hv).1))

end YM.RegulatorIR.Binding
