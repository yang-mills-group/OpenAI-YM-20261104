import YM.MatchingLedger.Sites
import YM.MatchingLedger.Ensemble
import YM.Next.UV_STRESS.Product
import YM.Branch.Covariant

/-!
# Preserve the vacuum far from a window while replacing links, in the physical step

There is only ONE frame choice per coarse site, and likelihood depends on the configuration.
All nearby tags (including a ring along the window) are resummed, so we need not lower
bound the term with particular tags after changing the field: it may even vanish.
Work with the tag sum before estimating ratios and powers of the pointwise densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Action
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision
open PatchArea Push.SectorMeasure MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

section scan
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
def survey (w : X→Y→ℝ) (f : (X→Y)→ℝ) := ∑ x:X→Y, (∏ i,w i (x i))* f x

def uses (p : X → Prop) (f : (X→Y)→ℝ) := ∀ x y, (∀ i,p i → x i=y i) → f x=f y
variable {p : X→Prop} [DecidablePred p] [Nonempty Y]
include p in
lemma survey_congr {w g : X→Y→ℝ} {f : (X→Y)→ℝ} (hf : uses p f)
    (hw : ∀ i, (∑ x,w i x)=1) (hu : ∀ i, (∑ x,g i x)=1) (he : ∀ i,p i → w i=g i) :
    survey w f=survey g f := by
  apply Complex.ofReal_injective
  have h : Next.UVStress.Draws p (fun x=>(f x:ℂ)) := fun x y h=> congr_arg _ (hf x y h)
  unfold survey; push_cast; refine Next.UVStress.scanning_congr p (fun i z=>(w i z:ℂ)) (fun i z=>(g i z:ℂ)) _ _ h h ?_ ?_ (fun i hi=>by rw [he i hi]) rfl
  · intro i; rw [← Complex.ofReal_sum,hw]; rfl
  intro i; rw [← Complex.ofReal_sum,hu]; rfl
end scan

variable {c f : Side} (S : StepData c f) {G : Gauge}
variable (hB : S.patch.Branches S.kernel G)

def opinion (U : Config G f) (F : S.Choices→ℝ) := ∑ t,S.likelihood U t * F t

def sitePrice (U : Config G f) (x : Site c) := S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U)
def bondPrice (U : Config G f)(t : S.SitesChoice) (e : Bond c) := S.patch.predictorMass S.kernel (S.connector U t e)

theorem opinion_pay (U : Config G f) (F : S.Choices → ℝ) :
    opinion S U F = survey (sitePrice S U) (fun x=> survey (bondPrice S U x) (fun y=> F (x,y))) := by
  unfold opinion survey StepData.likelihood; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _=> (mul_assoc ..))

lemma opinion_scale (U : Config G f) (F : S.Choices → ℝ) (k : ℝ) :
    opinion S U (fun t=> k*F t)=k*opinion S U F := by unfold opinion; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>mul_left_comm ..)
lemma opinion_mono (U : Config G f) (F H : S.Choices → ℝ) (h : ∀ t, Alive S U t → F t≤ H t) :
    opinion S U F≤opinion S U H := by
  apply Finset.sum_le_sum; intro t _; by_cases ht : Alive S U t
  · exact mul_le_mul_of_nonneg_left (h t ht) (S.likelihood_pos ..)
  rw [dead ht]; simp

include hB in
lemma opinion_pos (U : Config G f) (F : S.Choices → ℝ) (h : ∀ t, 0 < F t) : 0 < opinion S U F := by
  obtain ⟨t,-,he⟩:= Finset.exists_ne_zero_of_sum_ne_zero (f:=S.likelihood U) (by rw [S.chosen hB U]; exact one_ne_zero)
  exact Finset.sum_pos' (fun i _=>mul_nonneg (S.likelihood_pos ..) (h i).le) ⟨t,Finset.mem_univ _,mul_pos (lt_of_le_of_ne (S.likelihood_pos ..) he.symm) (h t)⟩

-- A general score comparison in the same grouping. Need moment equality on all outside
-- entries, irrespective of whether a particular outside choice was the tag of a tested path.
private def sitesOf (S : StepData c f) (R : Support c) (i : Site c) := i∉halo (radius S.patch) R
private def bondsOf (S : StepData c f) (R : Support c) (e : Bond c) := e.1∉halo (belt S.patch) R

variable {R : Support c}{U W : Config G f} (V : Config G c) (h : ExteriorEq S R U W)
include hB
omit hB in
private lemma bonds_off (i : Bond c)(hi : bondsOf S R i) : sitesOf S R i.1 ∧ sitesOf S R (i.1+step i.2) :=
  ⟨fun hp=> hi (Lattice.Corona.halo_mono (show radius S.patch ≤ belt S.patch from by unfold belt; omega) (Finset.Subset.refl _) hp),
   away (R:=R) (k:=2) hi ((Work.E01.sep_step_le ..).trans (by omega))⟩
include h
private lemma connector_left (a b : S.SitesChoice) (hh : ∀ i, sitesOf S R i → a i=b i) (i : Bond c) (hi : bondsOf S R i) :
    S.connector U a i=S.connector W b i := Push.GridApprox.connector_dep S hB i a b (hh _ (bonds_off S i hi).1)
      (hh _ (bonds_off S i hi).2) (through S h (bonds_off S i hi).1) (through S h (bonds_off S i hi).2)
-- fix signature
private lemma equal_out {e t : S.Choices} (hh : ∀ i, sitesOf S R i → e.1 i=t.1 i)
    (hu : ∀ i, bondsOf S R i → e.2 i=t.2 i) :
    total (halo (belt S.patch) R)ᶜ (bill S U V e)= total (halo (belt S.patch) R)ᶜ (bill S W V t) := by
  apply Finset.sum_congr rfl; intro x hx
  have hd (i : Axis) : bondsOf S R (x,i) := Finset.mem_compl.mp hx
  have hE : x∉halo (radius S.patch) R:= (bonds_off S (x,0) (hd 0)).1
  have hN : face S U x= face S W x:= Finset.sum_congr rfl fun i hi=> congr_arg (· ^ 2) (faces S h i (by rw [Finset.mem_singleton.mp (loc.mp hi)]; exact hE))
  unfold bill; rw [hN]; apply congrArg (fun X=> (1/2:ℝ)*face S W x + (S.kernel.penalty/2)*X)
  apply Finset.sum_congr rfl; intro i _; unfold wire StepData.prediction
  rw [connector_left S hB h _ _ hh _ (hd i),hu _ (hd i)]

def untapped (R : Support c) (β : ℝ)(U : Config G f)(V : Config G c) := opinion S U
      (fun t=>Real.exp (-β * total (halo (belt S.patch) R)ᶜ (bill S U V t)))
lemma far_charge (β : ℝ) : untapped S R β U V=untapped S R β W V := by
  rw [untapped,opinion_pay,untapped,opinion_pay]; let p := sitesOf S R; let k:=bondsOf S R
  let L (U : Config G f)(t : S.Choices) : ℝ := Real.exp (-β * total (halo (belt S.patch) R)ᶜ (bill S U V t))
  let f' (U : Config G f)(t : S.SitesChoice) : ℝ:= survey (bondPrice S U t) (fun y=>L U (t,y))
  have hx (U W : Config G f) (h : ExteriorEq S R U W) (e d : S.SitesChoice) (hp : ∀ i,p i→ e i=d i) : f' U e=f' W d:=by
    have hh : uses k (fun y=>L U (e,y)) := fun x y hr=> congr_arg (fun t=>Real.exp (-β*t)) (equal_out S hB V (show ExteriorEq S R U U from fun _ _=>rfl) (fun _ _=> rfl) hr)
    have hu : (fun y=> L W (d,y))=(fun y=>L U (e,y)):= funext (fun y => congr_arg (fun t=>Real.exp (-β*t)) (equal_out S hB V h (e:=(e,y)) (t:=(d,y)) hp (fun _ _=>rfl)).symm)
    unfold f'; rw [hu]; exact survey_congr hh (fun i=> S.patch.predictorMass_sum ..) (fun i=> S.patch.predictorMass_sum ..) (fun i hi=>by unfold bondPrice; rw [connector_left S hB h e d hp i hi])
  change survey (sitePrice S U) (f' U) = survey (sitePrice S W) (f' W)
  rw [← show f' U=f' W from funext fun t=> hx _ _ h t t (fun _ _=>rfl)]
  exact survey_congr (p:=sitesOf S R) (hx U U (fun _ _=>rfl)) (fun i=>S.patch.frameMass_sum hB _) (fun i=>S.patch.frameMass_sum hB _) (fun i hi=>funext fun v=>(Push.GridApprox.site_dep S hB i (through S h hi) v).2)

-- density/license
omit h
section issued
variable (β : ℝ)
def probative (β : ℝ) (V : Config G c) (U : Config G f) : ℝ := opinion S U
  (fun t=>Real.exp (-β*total Finset.univ (bill S U V t)))

omit hB in
theorem total_exact (t : S.Choices) (U : Config G f) :
    total Finset.univ (bill S U V t)= energy U + S.kernel.penalty * ∑ e:Bond c, G.price (V e*(S.prediction U t e)⁻¹) := by
  unfold bill; rw [total_add,total_scale,total_scale]; congr 1
  · unfold total face; rw [total_at (region S) (fun i=>toll U i^2),loc_all]; unfold toll; simp_rw [G.chord_price]; rw [← Finset.mul_sum,← mul_assoc]; norm_num; rfl
  rw [Fintype.sum_prod_type]; unfold total thread wire; simp_rw [G.chord_price]; rw [Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.mul_sum,← mul_assoc]; ring

def cushion (G : Gauge) (S : StepData c f) (β : ℝ) : ℝ :=
  ((S.penaltyZ β G)⁻¹)^(Fintype.card (Bond c))
omit hB in
lemma cushion_pos : 0 < cushion G S β:= pow_pos (inv_pos.mpr (S.penaltyZ_pos ..)) _

-- left is literally what the top transfer is integrating.
omit hB in
lemma copper (U : Config G f) : S.density β U V * Wilson.bare β U=
    cushion G S β * probative S β V U := by
  unfold StepData.density; rw [Finset.sum_mul]; unfold probative opinion; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _
  let f (e : Bond c):ℝ:= G.price (V e*(S.prediction U t e)⁻¹)
  have hx : S.noise β (S.prediction U t) V=cushion G S β* Real.exp (-β*S.kernel.penalty * ∑ e, f e):=by
    unfold StepData.noise; rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]; rw [Finset.prod_const]; rfl
  dsimp only; rw [hx,total_exact,mul_add,Real.exp_add]; unfold Wilson.bare f; ring_nf
lemma pulse (U : Config G f) : 0<probative S β V U := opinion_pos S hB _ _ (fun _=> Real.exp_pos _)
lemma counted : Envelope (probative S β V) := by
  let T:= S.isKernel hB β; obtain ⟨C,hC⟩:= T.bound
  have hp : Measurable (fun U=> S.density β U V):= by
    let I(U:Config G f) : Config G f × Config G c := (U,V)
    exact (show Measurable ((fun w: Config G f × Config G c => S.density β w.1 w.2) ∘ I) from T.meas.comp (show Measurable I from measurable_id.prodMk measurable_const))
  have hv : Envelope (fun U=> S.density β U V):=
    ⟨hp, C,fun U=>(Real.norm_of_nonneg (T.positive U V)).trans_le (hC U V)⟩
  obtain ⟨a,ha⟩ := (bare_cont β (G:=G) (n:=f)).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  rw [show probative S β V=(fun x=> (cushion G S β)⁻¹*(S.density β x V * bare β x)) by funext x; rw [copper S V β x, inv_mul_cancel_left₀ (cushion_pos S β).ne']]
  have hB : Envelope (fun x:Config G f => bare β x):= ⟨measurable_bare _,a,ha⟩
  exact (Envelope.const _).mul (hv.mul hB)
end issued

end YM.MatchingLedger.Action
