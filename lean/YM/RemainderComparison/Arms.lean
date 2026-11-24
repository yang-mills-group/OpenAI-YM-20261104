import YM.RemainderComparison.Relative
import YM.Next.WARD_BIN.Lies

/-!
# Ordered-left sparse denominator probes

Ordered paths, not claiming symmetry of left derivatives. Use before log/kinetic
reclosure, including upper derivative moments of a signed conditional comparison on
local coarse windows. Cost polynomial in union of those probed sites; no volume, period
or cutoff constant (for unrestricted probes of course that union can be large). This
slot is not costing the support of a representation -- just relative costs of the
conditional normalization/push. Lives on the group, no indicator differentiation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Relative
open Function Filter Finset Lattice RG Wilson MeasureTheory Push Push.Uniform
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat WardBin.Lies
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {l j : ℕ} {o : Finset (Edge (Site c))}

-- CLM masker over edge probes, NOT on fields/thresholds

def tap (o : Finset (Edge (Site c))) (l : ℕ) : Slab G c l →L[ℝ] Slab G c l :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun e : Edge (Site c) =>
    if e ∈ o then ContinuousLinearMap.proj e ∘L (ContinuousLinearMap.proj i : Slab G c l →L[ℝ] Directions G c)
    else 0

lemma tap_apply (h : Slab G c l) i e : tap o l h i e= if e∈o then h i e else 0 := by
  simp only [tap,ContinuousLinearMap.pi_apply]; split_ifs <;> rfl

lemma tap_univ (i : Slab G c l) : tap univ l i=i := by funext k e; rw [tap_apply,if_pos (mem_univ _)]

lemma tap_small (i : Fin l) (b : Edge (Site c)) :
    let L : Slab G c l →L[ℝ] G.Color := ContinuousLinearMap.proj b ∘L (ContinuousLinearMap.proj i : Slab G c l →L[ℝ] Directions G c) ∘L tap o l
    ‖L‖ ≤ 1 := by
  intro L; refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  change ‖tap o l z i b‖ ≤ 1*‖z‖
  rw [one_mul,tap_apply]
  split_ifs; exact (norm_le_pi_norm (z i) _).trans (norm_le_pi_norm z i)
  rw [norm_zero]; exact norm_nonneg _

def edgeScene (l : ℕ) (U : Config G c) (o : Finset (Edge (Site c))) := chug l U ∘ tap o l

lemma edgeScene_center (l : ℕ) (U : Config G c) : edgeScene l U o 0=U := by
  unfold edgeScene; rw [comp_apply, map_zero,chug_zero]

lemma still_scene {l : ℕ} {U : Config G c} (b : Edge (Site c)) (hb : b∉o) (i : Slab G c l) :
    edgeScene l U o i b=U b := by
  have hh n (A : Slab G c n) (V : Config G c) (ht:∀ i, A i b=0) : chug n V A b= V b := by
    induction n generalizing V with
    | zero => rfl
    | succ n ih =>
      simp only [chug]
      rw [ih (Fin.tail A) _ (fun i=>ht _), increment, ht]
      simp
  exact hh l _ _ (fun i=> by rw [tap_apply,if_neg hb])

def paintCost (G : Gauge) (l j : ℕ) (M : ℝ) : ℝ := (2^j*composeCost j M 1)^l * G.colorScale

variable (j) (U : Config G c) (o : Finset (Edge (Site c)))
lemma edgeJets (ℓ : ℕ) {m : ℝ} (hp : PaintSupply G j m) (x : Slab G c ℓ) (he : ‖x‖ < 1) :
    ∀ b, Allows j (fun y=> G.mat (edgeScene ℓ U o y b)) x (paintCost G ℓ j m) := by
  intro b
  let Q (l : ℕ) (A : Slab G c ℓ → Slab G c l) : Prop:= ∀ i : Fin l,
    ∃ L : Slab G c ℓ →L[ℝ] G.Color, ‖L‖ ≤ 1 ∧ (fun z : Slab G c ℓ => A z i b)=L
  let w:ℝ:=2^j*composeCost j m 1
  have hv n (A : Slab G c ℓ → Slab G c n) (V : Slab G c ℓ → Config G c) (p : ℝ)
      (hf : Allows j (fun y=>G.mat (V y b)) x p) (hq: Q n A) :
      Allows j (fun y=>G.mat (chug n (V y) (A y) b)) x (w^n*p) := by
    induction n generalizing p V with
    | zero => rw [pow_zero,one_mul]; exact hf
    | succ n ih =>
      have hQ : Q n (fun y=> Fin.tail (A y)) := fun i=> hq i.succ
      obtain ⟨L,hL,h⟩:= hq 0
      have hx : ‖L x‖ ≤ 1 := (L.le_opNorm _).trans ((mul_le_mul hL he.le (norm_nonneg _) zero_le_one).trans_eq (mul_one _))
      have hh:= (hp.2 (L x) (hx.trans (shade_one G))).comp (f:=fun y=> L y) (allows_linear hL hx)
      have ht: Allows j (fun y=> G.mat (increment (V y) (A y 0) b)) x (w*p) := by
        simp_rw [increment, congr_fun h]
        exact hh.times (f:=fun y=>G.lieExp (L y)) (g:=fun y=> V y b) hf
      rw [pow_succ,mul_assoc]
      exact ih _ (fun y=>increment (V y) (A y 0)) _ ht hQ
  apply hv ℓ (tap o ℓ) (fun _=>U) _ (allows_const _ (le_of_eq (Gauge.unitary_frob (G.mat_mul_star (U b)))))
    (fun i=> ⟨_,tap_small (G:=G) (o:=o) i b,rfl⟩)

lemma edge_window (l : ℕ) {m : ℝ} (hp : PaintSupply G j m) : Window o (edgeScene l U o) 0 j (paintCost G l j m) := by
  have h : ‖(0:Slab G c l)‖<1 := by rw [norm_zero]; exact zero_lt_one
  refine ⟨(edgeJets j U o l hp 0 h (Classical.arbitrary _)).nonneg,fun i hi y=> ?_,?_⟩
  · rw [edgeScene_center]; exact still_scene i hi y
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds h)] with x hx i _ using
    edgeJets j U o l hp x hx i

lemma supported_derivative {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ : Config G c → F} (A : Slab G c l) (hp : ∀ e ∉ o, ∀ i, A i e = 0)
    (hg : ContDiffAt ℝ l (f₁ ∘ chug l U) 0) {u v : ℝ}
    (h : Brush j u v (f₁ ∘ edgeScene l U o) 0) (hl : l≤j) :
    ‖leftDerivs f₁ (List.ofFn A) U‖ ≤ u*v^l*∏ i, ‖A i‖ := by
  let L := tap (G:=G) o l
  let B : Fin l → Slab G c l:= fun i=> Pi.single i (A i)
  have hb i : L (B i)=B i:= by
    funext j e; unfold L; rw [tap_apply]
    by_cases he:e∈o
    · rw [if_pos he]
    rw [if_neg he]; by_cases h:i=j
    · subst j; simp [B,hp e he]
    simp [B,h]
  let D:= f₁ ∘ edgeScene l U o
  have hh : iteratedFDeriv ℝ l D 0 B=iteratedFDeriv ℝ l (f₁ ∘ chug l U) 0 B := by
    change iteratedFDeriv ℝ l ((f₁ ∘ chug l U) ∘ L) 0 B= _
    rw [liner L (by rw [map_zero]; exact hg), map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp_rw [hb]
  rw [expand_part A hg,mixed_eval,← hh] -- B defeq?
  refine ((iteratedFDeriv ℝ l D 0).le_opNorm B).trans ?_
  simp_rw [B,Pi.norm_single]; exact mul_le_mul_of_nonneg_right (h.order l hl) (by positivity)

end YM.RemainderComparison.Relative
