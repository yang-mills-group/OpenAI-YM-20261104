import YM.RegulatorIR.Binding.Own
import YM.RegulatorIR.Centered.View

/-! Consumer connection before concrete RG estimates. Common physical-unit
positions, t log fields. Capsule doesn't require Stead on soft data or assume
actual PT coefficient statement. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore Tree Tree.Forest Step Ledger Ledger.Sky Uniform
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {W:Type}{M: W→ℕ} {G:Gauge} {p q e u h r s m:ℕ}
  {n:Page M→Side}
variable {S:Sky (fun _:Page M=> Long G.ColorIndex) (fun w=> Book G (n w))}
variable (T: S.Accounts)(Z:T.Report m)

-- Use even sides and ℓ Params. K not tied to a reference Gram convention.
structure Docket (S:Sky (fun _:Page M=> Long G.ColorIndex) (fun w=> Book G (n w))) where
 clock : Page M→ Binding.Scale
 rates : ∀ w,Horizon G (n w)→ℝ
 order : ∀ w:Flap M, StepData (n w.next) (n w.prev)
 connected : ∀ w:Page M, S.l w*(n w).val = S.P w.bindW
 even : ∀ w,Even (n w).val
 large : ∀ w,4≤(n w).val
 compatible : ∀ w, S.maps w=Geometry.Cart (S.l w) _ G.ColorIndex (even _) (connected _)
 bushes : ∀ w:Flap M, Tree.Forest (order w).ratio
 landscape : ∀ w : Flap M, Geometry.Field.Square (bushes w)
 legs : ∀ w,Nonempty (FitsO (S.frames w) (order w) (bushes w) (clock w.prev) (rates w.prev) (rates w.next))
 top : ∀ w,rates (Page.opening M w)=costO
 teeth w : (order w).patch.Branches (order w).kernel G

variable (D:Docket S) (F:Margins (fun w=> Book G (n w)))
abbrev TopF (n:Page M→ Side) (w:W):Side:=n (Page.opening M w)
abbrev TopHooks (n: Page M→Side)(G:Gauge)(w:W) := Hook G Empty (OEdge (TopF n w))
variable (A: ∀ w:W,TopHooks n G w)

def aliases (D:Docket S)(F:Margins (fun w=>Book G (n w))): Prop:=∀ w,Nonempty (ZeroO (D.rates (Page.finallyW M w)) (F.endK w) (F.haar w))
structure Coverage (s:ℕ): Prop where
 plan : ∀ w, Plan G (TopF n w) (A w)
 archive : ∀ w, Canvas G (D.clock (Page.opening M w)) (T.orb (Page.opening M w)) (A w) (Z.point (Page.opening M w)) s m
-- integrate step repeatedly
namespace Coverage
variable (H: Coverage T Z D A s)
include H
lemma craved : ∀ w,Nonempty (RangeR G (n w) (D.rates w) (goal (D.clock (Page.opening M w.bindW)) (A w.bindW)) s m (T.orb w) (Z.point w)):= by
 refine Page.proves ?_ ?_
 · intro w;rw [D.top]; exact arrive (H.plan w).tune (H.archive w) (D.even _) (H.plan w).law
 intro w h; obtain ⟨i⟩:=h; obtain ⟨p⟩:=D.legs w
 rw [← T.step_o w, ← Z.step_p w]; exact i.along (D.bushes w) (D.landscape w) (D.even _) (D.even _) (D.teeth w) p

-- exact all-order identity on the regulator (under stated primitive layer
-- compatibilities). same coupling entirely polynomial. arbitrary s shift.
lemma poem (U:aliases D F)(w) : plotPT (D.clock (Page.opening M w)) (A w) s = S.vista T Z F w := by
 obtain ⟨i⟩:= craved T Z D A H (Page.finallyW M w); obtain ⟨b⟩:= U w
 let k:= D.clock (Page.opening M w)
 have ht: storyPT k (A w)=fun a=> coeff a (PowerSeries.X ^ s*PowerSeries.mk (S.vista T Z F w)):= (top_truth k (A w) (D.even _) (H.plan w)).unique (RangeR.tongue i b (D.even ..))
 ext1 e; change storyPT k (A w) (s+e)= _; rw [ht]; dsimp only; rw [coeff_X_pow_mul',if_pos (Nat.le_add_right s e),show s+e-s=e from by omega, coeff_mk]

-- input discrepancy budget charged *after* this identity. no factor from
-- selecting the gauge in angular integration.
theorem amplitudes {k j: Choice M}{u b q p α h:ℕ}{c₀ γ:ℝ}{x:W→Room}{c:Flap M→ℝ≥0∞} {L:Meter W}
 (U:aliases D F)(P:S.Registry T Z L u b q p α h c₀ γ x k c) (E:S.Epoch F L u p)(he:e≤p)(hj:k.age ≤ j.age): Carry L (fun w=> ENNReal.ofReal (S.modifyErr h b γ j w)) fun w=> ‖plotPT (D.clock (Page.opening M w)) (A w) s e-note (Z.main (j.choose w) e 0)‖ₑ:= by
 simp_rw [H.poem T Z D F A U]
 letI : ∀ i:Page M,Fintype (Book G (n i)):=fun _=>inferInstance
 exact S.terminates T Z F E P he hj
end Coverage
end YM.RegulatorIR.Binding
