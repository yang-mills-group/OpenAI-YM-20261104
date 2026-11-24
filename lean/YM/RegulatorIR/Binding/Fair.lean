import YM.RegulatorIR.Centered.Breadth
import YM.RegulatorIR.Binding.Rosette
import YM.RegulatorIR.Cluster.Access

/-! IR-labeled endpoint during development. Genuine independent inversion
PT finite diagram coefficients in the comparison output; concrete hypotheses
remain substantial. This covers only internal Wilson diagram comparison with
this stencil/probe operation; further UV, OPE certificates and prescription
homomorphisms remain separate. Makes no assertion of actual asymptotic
following the formal construction except for the **fixed cutoff** Laplace
lemmas. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore Tree Tree.Forest Step Ledger Ledger.Sky Uniform Centered
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {W Z:Type}{M: W→ℕ} {G:Gauge} {p q e u h r s m α b:ℕ}
  {n:Page M→Side}

abbrev Ambient {W:Type} (G:Gauge) {M: W→ℕ}(n:Page M→Side):= Sky (fun _:Page M=> Long G.ColorIndex) (fun w=> Book G (n w))
variable (S:Ambient G n) (T:S.Accounts)(D:Docket S) (F:Margins (fun w=>Book G (n w)))
namespace Docket
variable (f:Z→W)
def admits : Docket (album S f):={ clock:=D.clock ∘ stages f M, rates:=fun w=>D.rates (stages f M w),order:=fun w=> D.order (arrow f M w),connected:=fun w=> D.connected (stages f M w),even:=fun w=> D.even (stages f M w),large:=fun w=> D.large (stages f M w),compatible:=fun w=> D.compatible (stages f M w), bushes:=fun w=> D.bushes (arrow f M w),landscape:=fun w=> D.landscape (arrow f M w),legs:=fun w=> D.legs (arrow f M w),top:=fun w=> D.top (f w),teeth:=fun w=>D.teeth (arrow f M w) }
lemma files (H:aliases D F): aliases (D.admits S f) (post F f):=fun w=> H (f w)
end Docket

variable {A: (u:plane W)→ TopHooks n G (film _ u)} (R:(movie T (film W)).Report m) {L:Meter W}{γ:ℝ}{c:Flap M→ℝ≥0∞}{k j:Choice M}

def reading (D:Docket S)(A : (u:plane W)→TopHooks n G (film _ u))(s:ℕ)(i:plane W):ℕ→ℝ:= plotPT (D.clock (Page.opening _ (film _ i))) (A i) s
def feature (D:Docket S)(A : (u:plane W)→TopHooks n G (film _ u))(s:ℕ)(e:ℕ)(w:W):ℝ:= weigh (same (S.P w /8)) (S.P w /8) fun x=> reading S D A s (w,x) e
-- independent of x fixed view

lemma at_origin (U:aliases D F) (h:Coverage (movie T (film W)) R (D.admits S (film W)) A s) (w:plane W): reading S D A s w = outlook S T R F w:= h.poem _ _ _ _ _ (D.files S F (film W) U) w

lemma at_go (U:aliases D F)(hx:Coverage (movie T (film W)) R (D.admits S (film W)) A s)
 (H: Seated S T R F L u b q p h α γ c k)(he:e ≤ p)(hj:k.age ≤ j.age)
 (hg:∀ w, Centered.Rhythm (S.l (j.choose w)) (medium S T R j e w))
 (hi:∀ w, IntegrableOn (medium S T R j e w) (Centered.court (S.P w))) (hv:∀ w,IntegrableOn (fun x=> reading S D A s (w,x) e) (Centered.court (S.P w))) :
 ∃ K:ℝ,∃ t:ℕ,0≤K∧∀ w, ‖feature S D A s e w-diffuse S T R j e w‖ ≤ K*(L.val w).toReal^t*(S.modifyErr h b γ j w+ S.l (j.choose w)/S.P w) := by
 unfold feature; simp_rw [at_origin S T D F R U hx] at hv ⊢
 letI : ∀ w, Fintype (Book G (n w)):= fun _=>inferInstance
 exact integrated S T R F H he hj hg hi hv
end YM.RegulatorIR.Binding
