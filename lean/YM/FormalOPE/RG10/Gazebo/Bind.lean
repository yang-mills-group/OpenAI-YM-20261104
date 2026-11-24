import YM.FormalOPE.RG10.Gazebo.Frost
/-! Convert **exactly** the free point stabilizer used on the perturb convention's physical
field quotient (same C/F chosen). Only the free theory and real tangent. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k n:ℕ}
local notation "𝒩" d=> tents F d
local notation "α"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) (PertExtension.Physical.Profile.n)

local notation "W" => Pert.Position.E F d
local notation "wk"=> Pert.Position.wickReading F d
open Pert.Position

private abbrev sumOn (q: Fin n→Deck F d) : Fin n→ W:= deck F d ∘ q
private def gust (A:𝒩 d)(t: Test n) : MultilinearMap ℂ (fun _ : Fin n=> W) ℂ:= ∑ i:Fin n,(wk t).compLinearMap (update (fun _=> LinearMap.id) i (Physical.operator (L:=Maxwell.standard F) (deck F d) A.val))
private abbrev latch (t:Test n)(q:Fin n→Deck F d) := (⟨⟨n,t⟩,q⟩:ℳ d)
lemma shines_back (q:Fin n→Deck F d) (t:Test n) : raw F d (latch t q)= Complex.re ((wk t) (sumOn q)):= by unfold raw Physical.free Physical.reading readingC; change Complex.re (t.applyTo _)= _; simp_rw [one_smul]; rfl
lemma gust_line (A:𝒩 d)(t: Test n)(u:Fin n→W) : gust A t u= ∑ i:Fin n,wk t (update u i ((buf A).val (u i))) := by
 unfold gust; rw [_root_.sum_apply]; apply sum_congr rfl; intro i _; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg; funext j; by_cases h:i=j; subst j; simp only [Function.update_self]; rfl
 rw [update_of_ne (Ne.symm h),update_of_ne (Ne.symm h)]; rfl
lemma feedback_beam (t:Test n)(q:Fin n→Deck F d)(A:𝒩 d): beam (latch t q) A= Complex.re (gust A t (sumOn q)) := by
 rw [gust_line,Complex.re_sum]
 change ∑ i:Fin n, (∑u:Deck F d, raw F d (latch t (update q i u))* A.val (q i) u)= _
 apply sum_congr rfl; intro i _; let b:= deck F d; let M:= (wk t).toLinearMap (sumOn q) i
 change _= (M ((buf A).val (b (q i)))).re
 rw [show (buf A).val (b (q i))= ∑ j,(A.val (q i) j:ℂ) • (b j) from Physical.operator_basis (L:=Maxwell.standard F) (deck F d) A.val (q i),map_sum]; simp_rw [map_smul, Complex.re_sum]; apply sum_congr rfl; intro s _; rw [shines_back]; change _= ((↑(A.val (q i) s):ℂ) * M (b s)).re; rw [Complex.re_ofReal_mul,mul_comm]
 have he : sumOn (F:=F) (update q i s) = update (sumOn q) i (b s) := by funext j; by_cases h:i=j; subst j; simp only [sumOn,Function.comp_apply,update_self]; rfl; rw [update_of_ne (Ne.symm h)]; change b (update q i s j)=_; rw [update_of_ne (Ne.symm h)]; rfl
 rw [he]; rfl

lemma absolute_slice (A:𝒩 d)(z:ℂ)(t:Test n)(u:Fin n→W) : gust A (z • t) u=z*gust A t u := by
 rw [gust_line,gust_line,Finset.mul_sum]; apply sum_congr rfl; intro j _; let q:=update u j ((buf A).val (u j)); change (∫ x,(z • t) x * Pert.Position.visible F d x q)= z*(∫x,t x* Pert.Position.visible F d x q); simp_rw [show ∀ x:Points n, (z • t) x = z • t x from fun x=> rfl,smul_eq_mul,mul_assoc]; rw [integral_const_mul]

lemma all_beam (hf: Pert.Position.Frozen F d)(B:𝒩 d)(he:∀ z:ℳ d, beam z B=0) : B=0 := by
 apply loyalty _; apply Pert.Position.detected F d hf (buf B)
 rintro ⟨n,q,t⟩; have hu (z:Fin n→Deck F d) : gust B t (sumOn z)=0:= by
   apply Complex.ext; exact (feedback_beam t z B).symm.trans (he ..)
   have h:= (feedback_beam (Complex.I • t) z B).symm.trans (he ..); rw [absolute_slice, Complex.mul_re] at h; exact neg_eq_zero.mp (by simpa using h)
 rw [Pert.Position.feedback_eq]; change Complex.re (∑ i:Fin n, Pert.Position.wickReading F d t (update q i _))=0; rw [← gust_line];
 have hz : (∑ u:Fin n→Deck F d,(∏i,(deck F d).repr (q i) (u i)) • gust B t (sumOn u))=gust B t q:= by
   conv_rhs=> rw [←funext (fun i=> (deck F d).sum_repr (q i))];
   rw [MultilinearMap.map_sum]; apply sum_congr rfl; intro u _; exact (MultilinearMap.map_smul_univ (gust B t) (fun i=> (deck F d).repr (q i) (u i)) _).symm
 rw [← hz]; simp [hu]
end YM.FormalOPE.RG10.Gazebo
