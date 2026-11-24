import YM.PREC.Derivative
import YM.RG02.Wick.Tags

/-!
Probability conventions. The factor stripped from this finite volume local
numerator is the *actual* normalized score multiplier (preserves E2 reset).
It can be scalarly expanded after the calculation if needed. Predictor branch
admits uniform independent site/bond tags near the trivial sector. Use that
only there. Trees used to calculate later can be additional independent finite
tags common to the step, not confused with `Actors`. The beam assembled
at one tag must reconstruct all weights; averaging squared independent tag
copies or sampling a second tag for the same bond is NOT this scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Branch
open Filter Function MeasureTheory Set Lattice Wilson RG Precision Wick.Actor
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}(S : StepData c f)

/-- Branch predicate for interior. -/
def Inspected (U : Config G f) := (∀ x, S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) U)) ∧
     ∀ a : S.SitesChoice, ∀ e, S.patch.usesBest S.kernel (S.connector U a e)

lemma measurable_branch (h : S.patch.Branches S.kernel G) : MeasurableSet {u:Config G f| Inspected S u} := by
    simp only [Inspected, Set.setOf_and,Set.setOf_forall]
    refine (MeasurableSet.iInter (fun x=> ?_)).inter (MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun e=> (S.connector_meas h _ _) S.patch.best_open.measurableSet)))
    exact (by unfold expandAt; fun_prop : Continuous (fun U: Config G f => expandAt (S.ratio.embed x) U)).measurable (S.patch.min_open.measurableSet)

lemma inspected_one (h : S.patch.Branches S.kernel G) : Inspected S (1:Config G f) := by
   constructor
   · intro x; have h:= mem_of_mem_nhds (Push.threshold S x (G:=G))
     unfold Push.product at h; simpa only [Set.mem_setOf_eq, Precision.link_one] using h
   intro a e
   rw [← link_one]; change S.patch.bondCost _ _<_
   refine lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1) ?_
   change S.patch.bondCost (Push.deck S e a 0) (1:G.El)< S.kernel.predictor_cut
   simpa [Patch.bondCost,Push.deck_zero S h e a] using S.kernel.predictor_cut_pos

variable {U : Config G f}

lemma neighborhood (h : S.patch.Branches S.kernel G) (H : Inspected S U) :
    ∀ᶠ v in 𝓝 U, Inspected S v := by
   have hm x : Continuous (fun u : Config G f => expandAt (S.ratio.embed x) u) := by unfold expandAt; fun_prop
   have hu (x:Site c) : ∀ᶠ v in 𝓝 U,S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) v) :=
       ((hm x).tendsto U).eventually (S.patch.min_open.mem_nhds (H.1 x))
   refine (eventually_all.mpr hu).and (eventually_all.mpr (fun i => eventually_all.mpr fun e => ?_))
   have hv (x : Site c) : ContinuousAt (fun u' : Config G f => S.frames u' i x) U := by
      let F := fun u' : Config G f => S.patch.selected (expandAt (S.ratio.embed x) u')
      have hp : ContinuousAt F U := ((S.patch.selected_cont h).continuousAt (S.patch.min_open.mem_nhds (H.1 x))).comp (hm x).continuousAt
      apply hp.congr
      filter_upwards [hu x] with j hj
      simp only [StepData.frames,Patch.frame,if_pos hj,F]
   have he : ContinuousAt (fun v : Config G f => S.connector v i e) U := continuousAt_pi.mpr fun a =>
      (((continuous_apply a).continuousAt.comp (hv e.1)).mul
       (((continuous_travel ..).comp (hm e.1)).continuousAt)).mul
       ((continuous_apply a).continuousAt.comp (hv _)).inv
   exact he.eventually (S.patch.best_open.mem_nhds (H.2 i e))

lemma center_germ (h : S.patch.Branches S.kernel G) : ∀ᶠ u in 𝓝 (1:Config G f), Inspected S u := neighborhood S h (inspected_one S h)

lemma same_prediction (H : Inspected S U)(t i : S.Choices) : S.prediction U t=S.prediction U i := by
   have he (e) : S.connector U t.1 e=S.connector U i.1 e := by
     funext x; unfold StepData.connector StepData.frames; simp only [Patch.frame, H.1,↓reduceIte]
   unfold StepData.prediction; simp only [Patch.predict,he,H.2,↓reduceIte]

lemma cost (H : Inspected S U)(t : S.Choices) : S.likelihood U t=(Fintype.card S.Choices:ℝ)⁻¹ := by
   simp only [StepData.likelihood,Patch.frameMass,Patch.predictorMass,H.1,H.2,↓reduceIte,Finset.prod_const,Finset.card_univ]
   simp [StepData.Choices,StepData.SitesChoice,StepData.BondChoice,mul_pow,mul_comm]

def uniform (F : S.Choices→ℂ) := (Fintype.card S.Choices : ℂ)⁻¹ * ∑ i,F i
lemma uniform_actual (H : Inspected S U)(v : S.Choices→ℂ) : uniform S v = ∑ i:S.Choices,(S.likelihood U i:ℂ)*v i := by
   simp only [cost S H,uniform,Finset.mul_sum,Complex.ofReal_inv,Complex.ofReal_natCast]

abbrev Actors := Site c ⊕ Edge (Site c)
def Picks : Site c ⊕ Edge (Site c)→ Type := Sum.elim (fun _=>S.patch.FrameTag) (fun _=>S.patch.Points)
instance (z : Site c ⊕ Edge (Site c)) : Fintype (Picks S z) := by cases z <;> unfold Picks <;> dsimp only [Sum.elim] <;> infer_instance
instance (z : Site c ⊕ Edge (Site c)) : Nonempty (Picks S z) := by cases z <;> unfold Picks <;> dsimp only [Sum.elim] <;> infer_instance

def representActors : Draw (Picks S) ≃ S.Choices := Equiv.sumPiEquivProdPi ..

def publicLaw := expectation fun i (_ : Picks S i) => (Fintype.card (Picks S i) : ℂ)⁻¹
lemma public_independent : Multiplying (publicLaw S) := by
   apply contracting; intro i
   have hk : (Fintype.card (Picks S i) : ℂ)≠0 := by exact_mod_cast Fintype.card_pos.ne'
   simp [hk]
lemma public_uses (v : S.Choices→ℂ) : publicLaw S (v ∘ representActors S)=uniform S v := by
    let q := representActors S
    let D := fun i (x : Picks S i) => (Fintype.card (Picks S i) : ℂ)⁻¹
    have he i : joint D i=(Fintype.card S.Choices:ℂ)⁻¹ := by
       unfold joint; simp_rw [D]; rw [Finset.prod_inv_distrib,← Fintype.card_congr q]
       simp [Fintype.card_pi,Draw]
    change ∑ i : Draw (Picks S),joint D i * v (q i)= _; simp_rw [he];
    rw [← Finset.mul_sum,Equiv.sum_comp]; rfl

/-- Exact (potentially cutoff dependent) noise scalar. Keep it outside the
unnormalized Markov calculation and restore in cost assertions. -/
def noisePrefactor (β : ℝ)(G : Gauge) := ((S.penaltyZ β G)⁻¹)^ Fintype.card (Edge (Site c))
lemma noisePrefactor_pos (β : ℝ)(G : Gauge) : 0<noisePrefactor S β G := pow_pos (inv_pos.mpr (S.penaltyZ_pos β)) _
lemma noise_factor (U : Config G f)(V : Config G c)(i : S.Choices)(β : ℝ) :
    S.noise β (S.prediction U i) V=noisePrefactor S β G* Real.exp (-β * noiseTaylor S V U i) := by
   rw [StepData.noise,Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
   unfold noisePrefactor StepData.penaltyWeight
   rw [← Real.exp_sum]; apply congr_arg
   unfold noiseTaylor; rw [← Finset.mul_sum,mul_assoc]
end YM.RG02.Branch
