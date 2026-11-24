import YM.SchemeRG11.Sew.Bed
/-! Segmented conversion and closure on remote peers. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical Pointwise
variable {G:Gauge} {m n:ℕ}
local notation "D₁" => Atoll.land G
lemma sensor(t:Cover): ((D₁).pull (Dose.arrow (rise t)))=(D₁):=by apply Dose.strict; intro i j; rw [Dose.reach]; simp [Atoll.land,rise]
lemma cross_h(t:Cover)(p:vellum G): cross t ((D₁).heat p)=(D₁).heat (cross t p):=by unfold cross; rw [Dose.migrate,sensor t]
lemma cross_n(t:Cover)(p:vellum G): cross t ((D₁).neg.heat p)=(D₁).neg.heat (cross t p):=by
 calc _= (D₁).neg.heat ((D₁).heat (cross t ((D₁).neg.heat p))) := ((D₁).opposite _).symm
      _= _:=by rw [←cross_h,Dose.reverse]
lemma cross_cov(t:Cover)(p:vellum G):(D₁).avg (cross t p)=(D₁).avg p:=by rw [cross,Dose.rebase,Dose.colour,sensor]
lemma cross_sum(t v:Cover)(p:vellum G):cross t (cross v p)=cross (t+v) p:=by simp only [cross,MvPolynomial.rename_rename]; unfold Function.comp; simp_rw [rise_form]
lemma cross_leaf(t:Cover)(a:Touch G): cross t (leaf a)=leaf (flex t a):=by induction a using Finsupp.induction_linear with
 | zero=>simp
 | add a b ha hb=>simp only [map_add,ha,hb]
 | single i b=> simp only [leaf,Finsupp.linearCombination_single]; rw [cross,map_smul,rename_X]; unfold flex; simp
lemma cross_lens(T: Align.Itinerary)(p:pLabel G)(a:ℕ → Cover)(i:ℕ): cross (a i) (castZero (T.gap i) p)=(D₁).neg.heat (vary (fun k=>lensLeg T k a i) p):=by
 rw [castFree,cross_n]; apply congrArg (D₁).neg.heat; change (cross (a i)) (stemZero _ _) = _
 have he:(cross (a i)).comp (stemZero (G:=G) (T.gap i))=vary (fun k=> lensLeg T k a i):=by ext k; rw [AlgHom.comp_apply,vary_X,vary_X,cross_leaf];rfl
 exact DFunLike.congr_fun he p
lemma cross_id(p:vellum G):cross 0 p=p:=by unfold cross; rw [show rise (G:=G) 0= _root_.id from funext fun z=>by simp [rise],rename_id]; rfl -- unused
-- exterior currency
abbrev Home : Subalgebra ℝ (ℕ→ℝ) where
 carrier:={f|Finishes f}
 algebraMap_mem' r:= Finishes.const r
 zero_mem' := Finishes.const 0
 one_mem' := Finishes.const 1
 mul_mem':=fun {_ _} h k=>Finishes.mul h k
 add_mem':=fun {_ _} h k=> Finishes.add h k
variable {T:Align.Itinerary}{r R:ℝ}{p:pLabel G}{B:Window}
def Brows(T: Itinerary)(R:ℝ):Set (ℕ→Touch G):={U|Blue T R (fun i=>(D₁).windfall (U i))}
lemma airlock {U:ℕ→vellum G}(p:∀ A, Blue T R A → Finishes (fun i=> aeval (A i) (U i))) (h:∀ i,Page _ m (U i)): Gate (D₁) Sew.Home (Brows T R) U:=by
 have ht(L: List (ℕ→Touch G))(hh:∀ i∈L,i∈Brows T R)(a:Falls G)(hp:Blue T R a): Finishes (fun i=>aeval (a i) (Sew.flood (D₁) L U i)):=by
    induction L generalizing U with
    | nil=>apply p _ hp
    | cons b L ih=>
      simp only [Sew.flood]; apply ih
      case p=> intro g hG; exact windy g (fun i=> (D₁).windfall (b i)) h (fun v=>p _ (show Blue T R (g+v • (fun i=> (D₁).windfall (b i))) from hG.add ((show Blue T R _ from (hh b (by simp) : b ∈ Brows T R)).scale v))) -- B as prop
      case h=> intro i; exact (h i).rim _
      case hh=> intro i hi; exact hh i (by simp [hi])
      -- HP auto
 exact fun L h=>ht L h 0 Blue.zero
lemma shift_in {F:Frames G}(h:IsWeightedHomogeneous generation p n)(v:Neutral p)(hp:B.rOut<r)(hv:r<R) :∃ m,∃ q:Fin m→ Tab F n,∃ M:ℕ→ Fin m→ℝ,(∀ a,Tendsto (fun i=>T.gap i*M i a) atTop (𝓝 0))∧ Gate (D₁) Sew.Home (Brows T R) (fun i=> (T.gap i)^(-(n:ℤ)) • (crestF p T B r i-∑ a:Fin m,M i a • stemZero 1 (q a).p)):=by
 obtain ⟨m,I,t,H,K⟩:= Wolt.output G F T B h v hp
 refine ⟨m,I,t,H,?_⟩
 obtain ⟨b,hb⟩:= critical p; choose c hc using fun i=> Page.crop (stemZero 1 (I i).p)
 let k:= Finset.univ.sup c
 apply airlock (m:=max k b)
 · intro A u; have hk:=K _ _ hv u; apply hk.same; filter_upwards with i; rw [map_smul];rfl
 intro i; refine Page.bill _ ((hb _ _).breathe (le_max_right ..) |>.sub (Page.sum _ _ (fun a ha=>?_))); exact .bill _ ((hc a).breathe (le_trans (Finset.le_sup (f:=c) ha) (le_max_left ..)))
variable {I:Type*}[DecidableEq I]
def Scores(T:Itinerary)(v : I→ℕ → Cover)(p:I)(i:ℕ)(k:Key G): Touch G:= lensLeg T k (v p) i
omit [DecidableEq I] in
lemma rocket(s:Finset I)(v:I→ ℕ → Cover)(c:I→pLabel G)(j:ℕ): aerial s (fun i=>castZero (T.gap j) (c i)) (fun i=>v i j)=screen (D₁) s (Scores T v) c j:=by unfold aerial screen; simp_rw [cross_lens];rfl
omit [DecidableEq I] in
lemma reachPrice(s:Finset I)(v:I→ℕ → Cover)(z:I→E4)(h:∀i∈s,Along T (v i) (z i))(hp:∀i∈s,∀j∈s,i≠j → z i≠z j) : priceS (D₁) (Scores T v) Sew.Home s:=by
 intro i hi j hj h' p q; change Finishes _; unfold Scores; simp_rw [lens_l]; exact intact (h i hi) (h j hj) (hp i hi j hj h') (high_probe _) (high_probe _)
lemma lights(s:Finset I)(v:I→ ℕ → Cover)(z:I→E4)(h:∀i∈s,Along T (v i) (z i))(hp:∀i∈s,∀j∈s,i≠j → z i≠z j)(he:∀i∈s,2*R< ‖z i‖)(p:I→pLabel G){U:ℕ→vellum G}(hq:Gate (D₁) Sew.Home (Brows T R) U): Finishes (fun i=> (D₁).avg ((D₁).neg.heat (U i)*aerial s (fun j=>castZero (T.gap i) (p j)) (fun j=> v j i))):=by simp_rw [rocket]; apply sailgate (D₁) (Scores T v) Sew.Home (Brows T R) s _ (reachPrice s _ _ h hp) p U hq; exact fun i hi k=> legit _ (h _ hi) (he _ hi)
end YM.SchemeRG11.Sew
