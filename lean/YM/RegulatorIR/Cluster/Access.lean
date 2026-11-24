import YM.RegulatorIR.Cluster.Figures
import YM.RegulatorIR.Ledger.Recovery

/-! Feed the general IR comparison: charge the engineering growth before
evaluation and supply it to the transmission budget, for ordinary and one
or more discrepancy stencils with optional ε^ζ. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z: Type}{M:W→ℕ} {X Y:Page M→Type} (S: Sky X Y)(T:S.Accounts){α:ℕ}(J:Composite I)
  {p e u r b n q:ℕ}{L:Meter W}
  {D:I→ W→Set Room}{d:W→ℝ}{m H:I→ℕ}{σ:I→ℝ}{t:W→ℝ≥0∞}
  {c:Flap M→ℝ≥0∞}{x:W→Room} {γ:ℝ} (k:Choice M)

lemma segmentM (G:Milieu S T u p L) : Milieu (k.before.expanse S) (k.before.part S T G.core) u p L:= ⟨k.before.sector S G.core, k.before.getN S G.sky G.core, fun w=>G.align (k.before.wing w),fun w=>G.mirror (k.before.wing w)⟩

variable (G: Milieu S T q p L)
variable (B:T.Report (J.accounts m))(R:S.Radiants L γ u α c k)
variable (A:I→(w:Page k.before.spans)→ Orders (X (k.before.page w)))
structure ClusterK (D:I→W→ Set Room)(d:W→ℝ)(x:W→Room)(σ:I→ℝ) (H:I→ℕ) (b:ℕ) : Prop where
-- R include externally
 stage : Expanse (k.before.expanse S) σ D J d x L
 front : Crown L (k.before.expanse S) (k.before.part S T G.core) A p (u+u+b) D (fun i=>topGrowth (k.before.expanse S) (σ i) (H i)) d m J
 -- need V follows and top gather
 atop : ∀ w, B.main (k.before.page (Page.opening _ w))= chargeC J A (Page.opening _ w)
 tilted : ∀ w i,i≤p→ (S.sight (k.before.wing w)).Way (B.main (k.before.page w.prev)) i
 thick : u+u+b≤q
-- force u explicit because implicit not used R

lemma given (Φ:ClusterK (u:=u) S T J k G B A D d x σ H b): Corporate (k.before.expanse S) (k.before.part S T G.core) A (fun w=> B.main (k.before.page w)) p m J := ⟨Φ.atop,fun w=>B.step_m (k.before.wing w), Φ.tilted⟩
include R
lemma convertsK (Φ:ClusterK (u:=u) S T J k G B A D d x σ H b){K:ℕ} (hb:K≤b)(h: Zodiac L (k.before.expanse S) (fun i=>topGrowth (k.before.expanse S) (σ i) (H i)) D J d K t x): S.Preserved T B t K p k x u L:=by
 intro i hi r
 have hG:= settled (T:= k.before.part S T G.core) (S:=k.before.expanse S) (segmentM S T k G) J h Φ.front (given S T J k G B A Φ) (k.before.restrict S R.lead) hb Φ.thick
 have hp: Carry (coverL k.before.spans L) (fun w=> (heightP (k.before.expanse S).l K w)⁻¹*t w.bindW) fun w=> markQ (S.coverQ x u (k.before.page w)) (B.main (k.before.page w) i r):=hG i hi r
 unfold Claim; convert hp using 1
 ext1 w; rw [heightP, ← ENNReal.ofReal_pow ((k.before.expanse S).hl w).le, ← ENNReal.ofReal_inv_of_pos (pow_pos ((k.before.expanse S).hl w) _)]; rfl
lemma base_power (Φ:ClusterK (u:=u) S T J k G B A D d x σ H b)(he:J.accounts H≤b): S.Preserved T B 1 (J.accounts H) p k x u L:= convertsK S T J k G B R A Φ he (Φ.stage.core J H)
lemma spare_power (Φ:ClusterK (u:=u) S T J k G B A D d x σ H b)(he:J.accounts H+n≤b)(ht:J.loss σ ≤ (n:ℝ)): S.Preserved T B (fun w=>ENNReal.ofReal (S.ε w^J.loss σ)) (J.accounts H+n) p k x u L:= convertsK S T J k G B R A Φ he (Φ.stage.improved J H ht)
end YM.RegulatorIR.Cluster
