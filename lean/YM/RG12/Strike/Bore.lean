import YM.RG12.Strike.Vertex
/-!
# Passing analytic derivatives along poke (commuting and trace)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {f g:R→ℂ}{S:Set R}(hS:IsOpen S)

-- punctual derivative at all required points. not at origin.
def silk (S:Set R)(f:R→ℂ):=∀ x∈ S, ContDiffAt ℝ ω f x
lemma gField {x:R}(hx:x≠0): ContDiffAt ℝ ω field x:=by
   have hf : field = Complex.ofRealCLM ∘(fun x:R=>(‖x‖^2:ℝ)⁻¹):= by funext; simp [field,black]
   rw [hf]
   exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((contDiff_norm_sq ℝ (E:=R)).contDiffAt.inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))
lemma drawing (x:R)(i:Axis4): HasDerivAt (palette i x) (bar i) (0:ℝ):=by
   have hf : HasDerivAt (fun s:ℝ=>s • bar i) ((1:ℝ) • bar i) 0:=(hasDerivAt_id' (0:ℝ)).smul_const _
   simpa only [one_smul] using! hf.const_add x
@[simp]lemma born (x:R)(i:Axis4):palette i x 0=x:=by unfold palette; simp
lemma along {x:R}(i:Axis4)(hf: DifferentiableAt ℝ f x): hit i f x = fderiv ℝ f x (bar i):=by
   have he:= hf.hasFDerivAt
   suffices h: HasDerivAt (fun z=>f (palette i x z)) (fderiv ℝ f x (bar i)) 0 from h.deriv
   have hh:HasFDerivAt f (fderiv ℝ f x) (palette i x 0):=by rw [born]; exact he
   exact hh.comp_hasDerivAt _ (drawing x i)
variable (h:silk S f){x:R}(hx:x∈S)
include hS h hx
lemma treads (i:Axis4) : hit i f =ᶠ[𝓝 x] fun y=>fderiv ℝ f y (bar i):= Filter.mem_of_superset (hS.mem_nhds hx) fun i' hi=> along _ ((h i' hi).differentiableAt (by decide))
omit hx in
lemma silken (i:Axis4): silk S (hit i f) := fun x hx=>by
   let L:= fderiv ℝ f; have he:= ContinuousLinearMap.apply ℝ ℂ (bar i)
   let w:(R→L[ℝ]ℂ)→L[ℝ]ℂ:=ContinuousLinearMap.apply ℝ ℂ (bar i)
   have hv: ContDiffAt ℝ ω (w ∘ L) x := w.contDiff.contDiffAt.comp _ ((h _ hx).fderiv_right (by exact le_top))
   exact hv.congr_of_eventuallyEq (treads hS h hx i)
-- iterated hit along list, and permutations
omit hx in
lemma vellum (L:Poke):silk S (barrage f L):=by induction L with
                                            | nil=>exact h
                                            | cons i b he=>exact silken hS he i
lemma twice (i j:Axis4): hit i (hit j f) x= hit j (hit i f) x:=by
   let L:= fderiv ℝ f
   have he(i j:Axis4):hit i (hit j f) x = fderiv ℝ L x (bar i) (bar j):=by
       rw [along _ ((silken hS h j x hx).differentiableAt (by decide)),(treads hS h hx j).fderiv_eq]
       let w:(R→L[ℝ]ℂ)→L[ℝ]ℂ:= ContinuousLinearMap.apply ℝ ℂ (bar j)
       change fderiv ℝ (w ∘ L) x (bar i)=_
       rw [fderiv_comp x w.differentiableAt ?_, w.fderiv]; rfl -- w fderiv def? simpl
       exact ((h _ hx).fderiv_right (le_top (a:=(1:ℕ∞ω)+1))|>.differentiableAt (by exact one_ne_zero))
   rw [he, he]; exact (h _ hx).isSymmSndFDerivAt_of_omega (bar i) (bar j)
omit h in
lemma in_turn (i:Axis4) (hf:∀ y∈S,f y=g y): hit i f x = hit i g x:=by
   unfold hit; apply Filter.EventuallyEq.deriv_eq
   have he : Tendsto (palette i x) (𝓝 (0:ℝ)) (𝓝 x):=by nth_rw 2 [show x = palette i x 0 from (born ..).symm]; exact (drawing x i).continuousAt.tendsto
   exact (he.eventually (hS.mem_nhds hx)).mono (fun z h=>hf _ h)
lemma regimen {K L:Poke}(hP:List.Perm K L): barrage f K x=barrage f L x:=by
   induction hP generalizing x with
   | nil=>rfl
   | cons i p he=> exact in_turn hS hx _ (fun z hz=>he hz)
   | swap i j l=> exact twice hS (vellum hS h l) hx _ _
   | trans h' h'' h1 h2=>exact Eq.trans (h1 hx) (h2 hx)

omit hS h hx in
lemma barrage_append (f:R→ℂ)(K L:Poke) (x:R):barrage f (K++L) x=barrage (barrage f L) K x:=by
   induction K generalizing x with
   | nil=>rfl
   | cons i K h=>change hit i (barrage f (K++L)) x= _; rw [funext h]; rfl
omit h hS hx in
lemma barrage_zero (K:Cells)(x:R): barrage 0 K x=0:=by
   induction K generalizing x with
   | nil=>rfl
   | cons a l H=> change deriv _ _ = _; simp_rw [comp_def,H]; rw [deriv_const]
-- commuting sums and scaling (scalar coefficients) to derivatives
omit h hS in
lemma thread {ι:Type}(T:Finset ι)(f:ι→R→ℂ)(h:∀ i∈ T,silk S (f i))(i:Axis4):
    hit i (∑ i∈T,f i) x=∑ j∈T, hit i (f j) x:=by
   let k:R:= palette i x 0
   have hk:k=x:=born ..
   have he (j)(hj:j∈T):blue i (f j) x:= ((h _ hj k (hk ▸ hx)).differentiableAt (by decide)).comp (0:ℝ) (drawing x i).differentiableAt
   unfold hit
   have hf: (∑ i∈T, f i) ∘ palette i x = ∑ a∈T, (f a) ∘ palette i x:=by funext; simp
   rw [hf,deriv_sum]; exact he
omit hS h hx in
lemma spin {x:R}(c:ℂ)(f:R→ℂ)(i:Axis4):
   hit i (fun x=> c*f x) x=c*hit i f x:=by change deriv (fun t=> c*((f ∘ palette i x) t)) 0 = _; rw [deriv_const_mul_field]
omit h in
lemma barrage_local {f g:R→ℂ}(he:∀ y∈ S,f y=g y)(K:Poke): barrage f K x=barrage g K x:=by
   induction K generalizing x with
   | nil=> exact he _ hx
   | cons i K ih=> exact in_turn hS hx _ (fun z hz=>ih hz)
-- test types
end YM.RG12.Strike
