import YM.RGComparison.Core16.Lumen.Spray
import YM.RGComparison.Core16.Therm.Pulse
/-!
# Sharing budget across gases

Local smooth payload catalogue. In-context witness priors genuinely preserve surveyed Word.
The smooth assumption excludes nonanalytic fallback ONLY using near-pocket suppliers, not on
all centered family cylinder values. No assumption equal densities or tag values on moved
far links. Everything on the whole tilted conditional gas rather than a smooth-outcome law.
Comparisons built through this hierarchy do NOT infer other height K/E estimates by this.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric
open Precision Forge Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge} {S:Side} {ι k T A D:Type} [Fintype ι] [Fintype k] [Fintype T] [Fintype D] -- omit [Fintype A] until finite coverage
abbrev Point (G:Gauge)(D:Type):= G.Color × (D→G.Color)
structure Shelf (G:Gauge)(A D:Type) where
   sector:Prices
   U:A→Point G D→ℝ
   R:ℝ
   δ:ℝ
   knot:ℝ
   Q:ℝ

structure Good (X:Shelf G A D):Prop where
   positive : 0<X.R
   extent : 0<X.δ ∧ X.δ<X.R
   thick : 0<X.Q ∧ 0<X.knot ∧ X.knot*X.Q<X.R
   reenter (x:G.El): G.chord x < X.δ→launch (G.curvature x)=x
   payment a:∀ x∈closedBall 0 X.R,ContDiffAt ℝ ω (X.U a) x
   smooth a: ContDiff ℝ ∞ (X.U a)
   zeroth a:X.U a 0=0
   first a: HasFDerivAt (X.U a) (0:Point G D→L[ℝ] ℝ) 0

structure Planet (X:Shelf G A D)(S:Side)(ι k T:Type) where
   loc:ι→Site S
   root:k→Site S
   meter:ℝ→ T→ Sky G ι → ℝ
   cost:ℝ→ T→ Sky G ι → k→ℝ
   glyph:k→A
   stem:k→ D→ Option ι
   ray:k→ G.Color

variable {X:Shelf G A D}
namespace Planet
variable (P: Planet X S ι k T)

def F (g:ℝ): Base G S ι k T:=⟨P.loc,P.root,P.meter g,P.cost g⟩
def portrait (p:D→ Option ι)(u:ι→G.Color)(i:D): G.Color := (p i).elim 0 u
def load (a:k)(g:ℝ)(x:Sky G ι): Point G D:= (g • P.ray a,portrait (P.stem a) (fun i=> G.curvature (x i)))
abbrev amen (X:Shelf G A D)(g:ℝ):Prop:=g∈Set.Icc 0 X.knot
abbrev crisp (z:ℝ)(I:Finset ι)(x:Sky G ι):Prop:=∀ i∈I,G.chord (x i)<z
omit [Fintype ι] in
lemma crisp_open (z:ℝ) (I:Finset ι):IsOpen {x:Sky G ι| crisp z I x}:=by
   rw [show {x:Sky G ι| crisp z I x}= ⋂ i:↥I, {x:Sky G ι|G.chord (x i) < z} from by ext v; simp [crisp]]
   exact isOpen_iInter_of_finite fun i=> isOpen_lt (by fun_prop) continuous_const
omit [Fintype ι] in
lemma crisp_negligible {v R:ℝ}(I J:Finset ι)(hv:v≤R)(hm:I⊆J){x:Sky G ι}(hc:crisp v J x):crisp R I x:= fun _ h => (hc _ (hm h)).trans_le hv

def tile (b:ℕ)(z : Site S):= neighborsOf P.loc b z
def soil (j:k):= P.tile X.sector.b (P.root j)
def heat (i:ι):= P.tile (2*X.sector.b) (P.loc i)
def AlwaysOff (i:ι)(x y: Sky G ι):=∀ j:ι,j≠i→x j=y j

structure Steady : Prop where
   prices: Good X
   tickets g : amen X g→ (P.F g).Admits X.sector g
   priced (a:k): ‖P.ray a‖≤X.Q
   thread (a:k)(u:D): ∀ i:ι,P.stem a u=some i → i∈P.soil a
   warm g: amen X g→∀ i:ι, ∀ x y:Sky G ι, AlwaysOff i x y→ crisp X.δ (P.heat i) x→ crisp X.δ (P.heat i) y→∀ s:T,P.meter g s x=P.meter g s y
   pay g: amen X g→∀ i:k,∀ x s, crisp X.δ (P.soil i) x→ P.cost g s x i=X.U (P.glyph i) (P.load i g x)
   outside g: amen X g→∀ i:k,∀ x y s, (∀ j∈P.soil i,x j=y j)→ P.cost g s x i=P.cost g s y i

omit [Fintype k] [Fintype T] [Fintype D] in
lemma loc_heat (i:ι) : i∈ P.heat i:= (member ..).2 (by simp)
def within (i:ι):= neighborsOf P.root X.sector.b (P.loc i)
omit [Fintype T] [Fintype D] in
lemma in_heat (i:ι)(a:k): i∈ P.soil a ↔ a∈ P.within i:= by rw [soil,tile,within,member,member,separation_comm]
omit [Fintype T] [Fintype D] in
lemma soil_heat {i:ι}{a:k}(h:a∈ P.within i): P.soil a ⊆ P.heat i:=by
     intro j hj; apply (member ..).2; refine (separation_triangle _ (P.root a) _).trans ?_; rw [two_mul]; exact Nat.add_le_add ((member ..).1 h) ((member ..).1 hj)

lemma load_calm (H:P.Steady)(a:k){x:Sky G ι}{g:ℝ}(h:amen X g)(hw: crisp X.δ (P.soil a) x): ‖P.load a g x‖ ≤ X.R := by
    unfold load; rw [Prod.norm_def,norm_smul]; refine max_le ?_ ?_
    · rw [Real.norm_of_nonneg h.1]; exact (mul_le_mul h.2 (H.priced a) (norm_nonneg _) H.prices.thick.2.1.le).trans H.prices.thick.2.2.le
    rw [pi_norm_le_iff_of_nonneg H.prices.positive.le]; intro i; change ‖portrait (P.stem a) _ i‖ ≤ X.R; unfold portrait;  rcases he:P.stem a i with _|j
    · exact (show ‖(0:G.Color)‖=0 from by simp).le.trans H.prices.positive.le
    exact ((G.curvature_norm _).trans_lt ((hw _ (H.thread a i j he)).trans H.prices.extent.2)).le
end Planet
end YM.RGComparison.Core16.Lumen
