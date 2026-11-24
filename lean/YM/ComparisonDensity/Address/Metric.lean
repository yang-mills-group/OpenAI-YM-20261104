import YM.Source.Local
import YM.Analysis.Homogeneous

/-! Real rooted addresses, independent of mesh period in units of the root cell; polynomially weighted test envelopes (sup-norm on positions, operator norm on Frechet derivatives) for any fixed support size and order D. We can also use exact on-cell tests retaining full jets, with evaluations on smooth extensions on ℝ⁴. Whole variant keeps test growing to degree W; no periodic extension assumed. Never includes field derivatives. Each mark gets its own function, may restrict totals later. No choice of support made from a test value. -/
set_option autoImplicit false
noncomputable section
namespace YM.ComparisonDensity.Address
open Function Filter Set Lattice Tensor
open scoped Topology BigOperators Classical ContDiff

abbrev Pos := Axis → ℝ
inductive Field
| whole | cell
def space : Field→ Set Pos
| .whole=> univ
| .cell=> Metric.closedBall 0 (1/2)
structure Orbit where
  field : Field
  D : ℕ
  W : ℕ
namespace Orbit
variable (U:Orbit) (f:Pos→ℂ)
-- superscript weights; set W large for monomial tests, at least through horizon+1. W can be large also on cell (same norm, constant equivalence). Derivative order D at will including required D=h+2.
-- stage gates choose from these pre costs
abbrev scope := space U.field
lemma dawn : 0 ∈ U.scope:= by cases hf:U.field<;>simp [scope,hf,space]
lemma convex : Convex ℝ U.scope:= by unfold scope; cases U.field<;>first|exact convex_univ|exact convex_closedBall ..

def height (x:Pos):ℝ:= (1+‖x‖)^U.W
lemma sky (x): 0<U.height x:= by unfold height; positivity
lemma rises {x y : Pos}(h:‖x‖≤‖y‖): U.height x≤ U.height y:= by unfold height; gcongr
@[simp] lemma flat : U.height 0=1:= by simp [height]

structure Bill (c:ℝ) : Prop where
    nonneg : 0 ≤ c
    orders : ContDiff ℝ (U.D:WithTop ℕ∞) f
    limits (k:ℕ) : k ≤ U.D → ∀ x∈U.scope, ‖iteratedFDeriv ℝ k f x‖≤ U.height x * c
namespace Bill
variable {U f}{g:Pos→ℂ}{c l:ℝ}
variable (h:U.Bill f c)
lemma zero : U.Bill 0 0:= ⟨le_rfl,contDiff_const,fun _ _ _ _=>by simp⟩
include h
lemma more (hc:c≤ l): U.Bill f l:= ⟨h.nonneg.trans hc,h.orders,fun i hi x hx=> (h.limits i hi x hx).trans (by gcongr; exact (U.sky _).le)⟩ -- need gr
lemma add (H:U.Bill g l): U.Bill (f+g) (c+l):= by
  refine ⟨add_nonneg h.nonneg H.nonneg,h.orders.add H.orders,fun i hi x hx=>?_⟩
  rw [iteratedFDeriv_add_apply ((h.orders.of_le (Nat.cast_le.mpr hi)).contDiffAt) ((H.orders.of_le (Nat.cast_le.mpr hi)).contDiffAt),mul_add]
  exact (norm_add_le ..).trans (add_le_add (h.limits i hi x hx) (H.limits i hi x hx)) -- fix dots
lemma sub (H:U.Bill g l): U.Bill (f-g) (c+l):= by
  refine ⟨add_nonneg h.nonneg H.nonneg,h.orders.sub H.orders,fun i hi x hx=>?_⟩
  rw [iteratedFDeriv_sub_apply ((h.orders.of_le (Nat.cast_le.mpr hi)).contDiffAt) ((H.orders.of_le (Nat.cast_le.mpr hi)).contDiffAt),mul_add]
  exact (norm_sub_le ..).trans (add_le_add (h.limits i hi x hx) (H.limits i hi x hx))
lemma smul (z:ℂ): U.Bill (z • f) (‖z‖*c):= by
  refine ⟨mul_nonneg (norm_nonneg _) h.nonneg,(h.orders.const_smul z),fun k hk x hx=>?_⟩
  change ‖iteratedFDeriv ℝ k (fun x=>z • f x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((h.orders.of_le (Nat.cast_le.mpr hk)).contDiffAt),norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h.limits k hk x hx) (norm_nonneg _)
end Bill

/-- weighted test space (supports over extension WHOLE; cell uses smooth full functions with seminorm on closed cell, label costs include that representation). -/
def Mood : Submodule ℂ (Pos→ℂ) where
   carrier := {f|∃ c,U.Bill f c}
   add_mem' := fun _ _=> by rename_i h h'; obtain ⟨c,h⟩:=h; obtain ⟨d,h'⟩:=h'; exact ⟨_,h.add h'⟩
   zero_mem' := ⟨0,Bill.zero⟩
   smul_mem' := fun z _ h=> by obtain ⟨c,h⟩:=h; exact ⟨_,h.smul z⟩
lemma admits (f: U.Mood): ∃ c,U.Bill f.val c:= f.property
end Orbit
-- Signatures over all extensions with these bills; U selects domain. Affine inverse mesh translation.
structure Dip where
   shift : Pos
   rate : ℝ
def Dip.arc (Y:Dip) (x:Pos):Pos:=Y.shift+Y.rate • x
def Dip.plant (Y:Dip) (f:Pos→ℂ) : Pos→ℂ:= f ∘ Y.arc
variable (Y:Dip){f:Pos→ℂ}{U:Orbit}{c:ℝ}
lemma Dip.smooth (g:ContDiff ℝ (U.D:WithTop ℕ∞) f) : ContDiff ℝ (U.D:WithTop ℕ∞) (Y.plant f) := g.comp (contDiff_const.add ((contDiff_id (𝕜:=ℝ)).const_smul Y.rate))
lemma Dip.links (k:ℕ)(h:ContDiff ℝ (k:WithTop ℕ∞) f)(x:Pos): iteratedFDeriv ℝ k (Y.plant f) x = Y.rate^k • iteratedFDeriv ℝ k f (Y.arc x):= by
   let L:=Y.rate • ContinuousLinearMap.id ℝ Pos
   have hd : ContDiff ℝ (k:WithTop ℕ∞) (fun t=>f (Y.shift+t)):= h.comp (contDiff_const.add contDiff_id)
   rw [show Y.plant f=(fun t=>f (Y.shift+t)) ∘ L from rfl, ContinuousLinearMap.iteratedFDeriv_comp_right _ hd _ le_rfl, iteratedFDeriv_comp_add_left] -- inspect
   ext1 v
   rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; change iteratedFDeriv ℝ k f (Y.arc x) (fun i=> Y.rate • v i)=_
   rw [(iteratedFDeriv ℝ k f (Y.arc x)).map_smul_univ (fun i=>Y.rate) v]; simp
lemma Dip.count (H: U.Bill f c) (hl:0≤ Y.rate)(i:ℕ)(hi:i≤ U.D){x:Pos}(he:Y.arc x∈ U.scope): ‖iteratedFDeriv ℝ i (Y.plant f) x‖ ≤ (Y.rate^i)*(U.height (Y.arc x)*c) := by
   rw [Y.links _ (H.orders.of_le (Nat.cast_le.mpr hi)),norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hl _)]
   exact mul_le_mul_of_nonneg_left (H.limits i hi _ he) (pow_nonneg hl _)
namespace Dip
structure Fits (V:Field) : Prop where
   positive : 0<Y.rate
   small : Y.rate≤1
   unit : ‖Y.shift‖ ≤ 1
   outer : MapsTo Y.arc (space V) (space V)
variable {Y}
lemma held (ht : Y.Fits U.field) (f:Orbit.Mood U) {c : ℝ}(hf:U.Bill f.val c) : U.Bill (Y.plant f.val) (3^U.W*c):= by
   refine ⟨mul_nonneg (by positivity) hf.nonneg,Y.smooth hf.orders,fun k hk x hx=>?_⟩
   have hg :=Y.count hf ht.positive.le k hk (ht.outer (show x∈space _ from hx))
   refine hg.trans (le_trans ((mul_le_of_le_one_left (mul_nonneg (U.sky _).le hf.nonneg) (pow_le_one₀ ht.positive.le ht.small))) ?_)
   rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hf.nonneg; unfold Orbit.height; rw [← mul_pow]
   have hl : ‖Y.arc x‖≤ 1+‖x‖:= by
      apply (norm_add_le ..).trans (add_le_add ht.unit ?_); rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.positive]; exact mul_le_of_le_one_left (norm_nonneg _) ht.small
   apply pow_le_pow_left₀ (by positivity) _; linarith [norm_nonneg x] -- syntax

/-- Same-space pull. Every derivative included before cost. -/
def drawn (U:Orbit)(Y:Dip)(ht:Y.Fits U.field) : U.Mood→ₗ[ℂ] U.Mood where
   toFun f := ⟨Y.plant f.val,let ⟨_,h⟩:=U.admits f; (show ∃ c,U.Bill _ c from ⟨_,held ht f h⟩)⟩
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
end Dip
end YM.ComparisonDensity.Address
