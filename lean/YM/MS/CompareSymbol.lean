import YM.MS.SymbolParts

/-! Factor heat-line estimates algebraically, using initial continuum vs lattice estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real
open scoped ContDiff
variable {ι E F G H A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- Note `g` need not be small (e.g. useful at a scaled frequency). -/
structure Like (T : Cost ι E) (S : Scale ι) (g : ι → ℝ) (f h : Kern ι E F) (p : Kern ι E ℝ) : Prop where
    lat : Costs T S f p
    std : Costs T S h p
    gain : Costs T S (fun i q=>f i q-h i q) (fun i q=>p i q*g i)
namespace Like
variable {f h f' h' : Kern ι E F} {l r : Kern ι E G} {T : Cost ι E} {S : Scale ι} {p p' : Kern ι E ℝ} {g : ι → ℝ}
lemma zero (hp:T.NN p) (hg:∀ i, 0≤g i) : Like T S g (fun _ _=> (0 : F)) (fun _ _=>0) p := by
    refine ⟨Costs.zero hp, Costs.zero hp,?_⟩; simp only [sub_self]
    exact Costs.zero fun i q h => mul_nonneg (hp i q h) (hg i)
lemma add (hx : Like T S g f h p) (h1 : Like T S g f' h' p) : Like T S g (fun i q=> f i q+f' i q) (fun i q=> h i q + h' i q) p := by -- h shadows
    refine ⟨hx.lat.add h1.lat,hx.std.add h1.std, ?_⟩
    simpa [add_sub_add_comm] using hx.gain.add h1.gain
lemma neg (hx : Like T S g f h p) : Like T S g (fun i q=>-f i q) (fun i q=>-h i q) p := by
    refine ⟨hx.lat.neg,hx.std.neg,?_⟩; simpa [sub_eq_add_neg,add_comm] using hx.gain.neg
lemma sub (hx : Like T S g f h p) (h1 : Like T S g f' h' p) : Like T S g (fun i q=> f i q-f' i q) (fun i q=> h i q-h' i q) p := by
    simpa only [sub_eq_add_neg] using hx.add h1.neg
lemma bilinear (B : F→L[ℝ] G→L[ℝ] H) (hx : Like T S g f h p) (hy : Like T S g l r p') :
    Like T S g (fun i q=> B (f i q) (l i q)) (fun i q=> B (h i q) (r i q)) (fun i q=> p i q*p' i q) := by
    refine ⟨Costs.bilinear B hx.lat hy.lat, Costs.bilinear B hx.std hy.std, ?_⟩
    let W := fun i q=> p i q * p' i q*g i
    have ha:= (Costs.bilinear B hx.lat hy.gain).raise (Cost.of_le (g:=W) fun i q _=> (mul_assoc ..).symm.le)
    have hb:= (Costs.bilinear B hx.gain hy.std).raise (Cost.of_le (g:=W) fun i q _=> (mul_right_comm ..).le)
    convert! ha.add hb using 1; ext; simp only [map_sub,_root_.sub_apply]; abel
lemma mul {f h f' h' : Kern ι E ℂ} (hx : Like T S g f h p) (hy : Like T S g f' h' p') :
    Like T S g (fun i q=> f i q * f' i q) (fun i q=> h i q * h' i q) (fun i q=>p i q*p' i q) := hx.bilinear (ContinuousLinearMap.mul ℝ ℂ) hy
lemma rmul {f h f' h' : Kern ι E ℝ} (hx : Like T S g f h p) (hy : Like T S g f' h' p') :
    Like T S g (fun i q=> f i q * f' i q) (fun i q=> h i q * h' i q) (fun i q=>p i q*p' i q) := hx.bilinear (ContinuousLinearMap.mul ℝ ℝ) hy
lemma same (hg : ∀ i, 0 ≤ g i) (hf : Costs T S f p) : Like T S g f f p := by
    refine ⟨hf,hf,?_⟩; simp only [sub_self]; exact Costs.zero fun i q h=> mul_nonneg (hf.nonneg i q h) (hg i)
lemma L (hx : Like T S g f h p) (A : F →L[ℝ] G) : Like T S g (fun i q=> A (f i q)) (fun i q=> A (h i q)) p := by
    refine ⟨hx.lat.L _,hx.std.L _,?_⟩; simpa only [map_sub] using hx.gain.L A
lemma sum {P Q : A → Kern ι E F} {s : Finset A} (h : ∀ i ∈ s, Like T S g (P i) (Q i) p) (hp : T.NN p) (hg : ∀ i, 0 ≤ g i) : Like T S g (fun i q=> ∑ a∈s,P a i q) (fun i q=>∑ a∈s, Q a i q) p := by
    classical
    induction s using Finset.induction with
    | empty => simpa using zero (F:=F) (S:=S) hp hg
    | insert a s ha IH => simpa only [Finset.sum_insert ha] using (h a (Finset.mem_insert_self ..)).add (IH (fun i hi=> h i (Finset.mem_insert_of_mem hi)))
end Like
end YM.MS
