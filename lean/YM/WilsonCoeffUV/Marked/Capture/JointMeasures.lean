import YM.WilsonCoeffUV.Marked.Bounds.Allocation
/-!
# Measures rather than sup of separate profile tests

Positive sign currency on independent labels implements full support TV:
a measure on bool × Plot simultaneously, integral over derivative axes.
Local on actual compact domains. Charges restore one summable polynomial
factor covering counts/paths in four-dimensional root stencil. No
identification of this repr with raw already-labeled masked inputs on the
physical side. Needed estimates use aligned analytic repr.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Address
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}
-- general Hahn helper. Table compact\n
section
variable [TopologicalSpace U][CompactSpace U][T2Space U]
abbrev Bel (U:Type):= Bool × U
local instance (U:Type)[TopologicalSpace U]: MeasurableSpace (Bel U):=borel _
local instance (U:Type)[TopologicalSpace U]: BorelSpace (Bel U):=⟨rfl⟩
abbrev Es (U:Type)[TopologicalSpace U]:= ContinuousMap U ℝ
variable (V:Submodule ℝ (Es U))
local instance : NormedAddCommGroup V:=inferInstance
local instance : NormedSpace ℝ V:=inferInstance
def pic : ℝ × V →ₗ[ℝ] Es (Bel U) where
   toFun p:= ⟨fun x=> p.1 + positiveP x.1 * p.2.val x.2, continuous_const.add (((continuous_of_discreteTopology (f:=positiveP)).comp continuous_fst).mul (p.2.val.continuous.comp continuous_snd))⟩
   map_add' a b:= ContinuousMap.ext fun x=>by simp [mul_add]; ring
   map_smul' c x:= ContinuousMap.ext fun x=>by simp; ring

def nibP (v: V→L[ℝ]ℝ) : ℝ×V →ₗ[ℝ] ℝ where
    toFun x:= ‖v‖*x.1+v x.2
    map_add' a b:=by simp [mul_add]; ring
    map_smul' a x:= by simp; ring
variable [Nonempty U]
omit [T2Space U] in
lemma aboveA (x:ℝ × V): ‖x.1‖+ ‖x.2‖≤‖pic V x‖:=by
   have hx i: ‖x.1‖+‖x.2.val i‖≤‖pic V x‖:=by
       have h0 : ‖x.1+positiveP false*x.2.val i‖≤‖pic V x‖:= ContinuousMap.norm_coe_le_norm (pic V x) (false,i)
       have h1 : ‖x.1+positiveP true*x.2.val i‖≤‖pic V x‖:= ContinuousMap.norm_coe_le_norm (pic V x) (true,i)
       simp [positiveP,Real.norm_eq_abs] at *; grind
   obtain ⟨u⟩:= ‹Nonempty U›; have hu:‖x.2‖≤ ‖pic V x‖-‖x.1‖:= (ContinuousMap.norm_le _ (by linarith [hx u,norm_nonneg (x.2.val u)])).mpr fun y=>by change ‖x.2.val y‖ ≤_; linarith [hx y]
   linarith

omit [T2Space U] in
lemma wager (v: V→L[ℝ]ℝ)(x:ℝ × V): ‖nibP V v x‖ ≤ ‖v‖*‖pic V x‖:=by
   change ‖‖v‖*x.1+v x.2‖ ≤ _; refine (norm_add_le _ _).trans ((add_le_add ?_ (v.le_opNorm x.2)).trans (show ‖v‖*‖x.1‖+‖v‖*‖x.2‖≤ _ from by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (aboveA V x) (norm_nonneg _)))
   exact le_of_eq (by rw [norm_mul,norm_norm])

local instance : NormedAddCommGroup (Es (Bel U)):=inferInstance
local instance : NormedSpace ℝ (Es (Bel U)):=inferInstance
local instance : NormedAddCommGroup (LinearMap.range (pic V)):=inferInstance
local instance : NormedSpace ℝ (LinearMap.range (pic V)):=inferInstance
omit [T2Space U] in
lemma unrib (v: V→L[ℝ]ℝ): ∃ A:Es (Bel U) →L[ℝ] ℝ, Monotone A ∧(∀ x, A (pic V x)= nibP V v x) ∧ A 1=‖v‖ := by
   obtain ⟨f,hf,hv⟩:= factoring (pic V).rangeRestrict (nibP V v) (LinearMap.surjective_rangeRestrict _) _ (norm_nonneg v) (show ∀ x, ‖nibP V v x‖≤ ‖v‖*‖(pic V).rangeRestrict x‖ from wager V v)
   obtain ⟨A,hg,hr⟩:= exists_extension_norm_eq (LinearMap.range (pic V)) f; have H (x): A (pic V x) = nibP V v x:= (hg ((pic V).rangeRestrict x)).trans (hf x)
   have he : A 1=‖v‖:=by rw [show (1:Es (Bel U))=pic V (1,0) from ContinuousMap.ext fun x=>by simp [pic],H]; simp [nibP]
   refine ⟨A,?_,H,he⟩
   have hp (x:Es (Bel U))(h:0≤x):0≤ A x:=by
       let Y:=‖x‖ • (1:Es (Bel U))-x; have hy: ‖Y‖≤‖x‖:= (ContinuousMap.norm_le Y (norm_nonneg _)).mpr fun y=>by
           have ht: 0≤x y:= h y; have hT:= le_trans (le_abs_self (x y)) (ContinuousMap.norm_coe_le_norm x y); simp [Y,Real.norm_eq_abs]; rw [abs_le]; constructor <;> linarith [norm_nonneg x]
       have hK:= (show A Y≤ ‖v‖*‖x‖ from (le_abs_self _).trans ((A.le_opNorm _).trans (mul_le_mul (hr.le.trans hv) hy (norm_nonneg _) (norm_nonneg _))))
       simp only [Y,map_sub,map_smul,he,smul_eq_mul] at hK; linarith
   intro f g h; simpa using hp (g-f) (show 0≤g-f from fun x=>sub_nonneg.mpr (h x))
private abbrev CC (V:Type)[TopologicalSpace V]:= CompactlySupportedContinuousMap V ℝ
lemma mixSigned (v: V→L[ℝ]ℝ) : ∃ μ: Measure (Bel U),μ.Regular ∧IsFiniteMeasure μ∧μ.real univ=‖v‖∧∀ f:V,v f= ∫ x, positiveP x.1*f.val x.2 ∂μ:=by
   obtain ⟨A,hA,h,h'⟩:=unrib V v
   let Λ : CC (Bel U)→ₚ[ℝ]ℝ:= {
       toFun x:=A x.toContinuousMap
       map_add' x y:= map_add A x.toContinuousMap y.toContinuousMap
       map_smul' r x:= map_smul A r x.toContinuousMap
       monotone' _ _ h:=hA h }
   let μ:= RealRMK.rieszMeasure Λ
   let vC (x:Es (Bel U)): CC (Bel U):=⟨x,HasCompactSupport.of_compactSpace _⟩
   have ht (x: Es (Bel U)) : (∫ y,x y ∂μ)=A x:= RealRMK.integral_rieszMeasure Λ (vC x)
   refine ⟨μ,inferInstanceAs (RealRMK.rieszMeasure Λ).Regular,inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure Λ)),?_,?_⟩
   · rw [←h',←ht]; simp
   intro f; simp_rw [show ∀ x:Bel U,positiveP x.1*f.val x.2=pic V (0,f) x from fun x=> Eq.symm (zero_add _),ht,h]; simp [nibP]
end

abbrev Post (D:ι→ℕ):=Bel (Plot D)
scoped instance : MeasurableSpace (Post D):=borel _
scoped instance : BorelSpace (Post D):=⟨rfl⟩
abbrev Tent (D:ι→ℕ):=∀ i,Embroider.Scroll (D i)
def pts (S:Finset ι)(T:Tent D)(x:Post D):= positiveP x.1 * ∏ i∈S,crease (T i) (x.2 i).1.2 (x.2 i).2.val
lemma voucher (S:Finset ι)(v: Pen D S): ∃ μ:Measure (Post D), μ.Regular ∧ IsFiniteMeasure μ ∧ μ.real univ=‖v‖ ∧ ∀ f:Tent D,touch (fun i=>page (D i) (f i)) S v=∫ x,pts S f x ∂μ:=by
    let _ : Nonempty (Plot D):=⟨fun i=> (⟨0,fun _=>0⟩,zeroC)⟩
    obtain ⟨μ,h,g,x,f⟩:= mixSigned _ v; exact ⟨μ,h,g,x,fun T=>f (seaMark (fun i=>page (D i) (T i)) S)⟩
end YM.WilsonCoeffUV.Wheel.Address
