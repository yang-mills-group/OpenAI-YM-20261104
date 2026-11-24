import YM.Comparison.RG02.Moving.Melt
/-!
# Normalization and passage to log with both grading markers

No estimate here on the polynomial division errors if evaluating these functions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving.Shift
open Function Filter Finset MeasureTheory YM.Marker YM.Multi Order Assembly Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace Path
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Primitives.GCC.Anchor
open scoped Topology BigOperators Classical ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V) (r : ℕ)
local notation "δ" => Grade R r
local notation "M" => Board R r
local notation "ψ" => axis R r
lemma base_tip : (axis R r).part ((M).quiet)=0 := by unfold axis; rw [Join.inject_right_quiet,lambda_quiet]
lemma bottom_tip : bottom R r (axis R r)= axis R r := by unfold axis bottom; simp only [AlgHom.comp_apply,Join.project_inject_right]
variable {R r}
variable {f g : ℝ→Grade R r} (h : Seen f) (p : Seen g) (hv : ∀ᶠ x in 𝓝 0,UnitLeading (f x))
lemma bottom_sight (k : ℕ) (f:ℝ→Grade R r) : sight (fun t=> bottom R r (f t)) k= bottom R r (sight f k) := by
   apply Join.both_parts; intro s i; simp_rw [sight_at,bottom_value]
   by_cases he:s=R.quiet; · simp only [he,if_true,sight_at]
   simp_rw [if_neg he,mconst]; simp
lemma stamp0 (F : ℝ→Grade R r) : (fuse R r F).part ((M).quiet)= (F 0).part ((M).quiet) := by
   rw [fuse_time,Poly.part_sum,sum_eq_single 0]; simp only [sight_0,pow_zero,mul_one]
   · intro i _ h
     rw [← blank_score,map_mul,map_pow,blank_score,blank_score,base_tip,zero_pow h,mul_zero]
   simp
lemma absorb (f : ℝ→Grade R r) : denominator (fuse R r f)=fuse R r (fun t=> denominator (f t)) := by
   unfold denominator; rw [fuse_time,fuse_time,map_sum]; simp_rw [map_mul,map_pow,bottom_tip, bottom_sight]
include h
lemma Seen.across : Seen (fun t=> denominator (f t)) := by
   constructor; intro i
   rw [← Join.pair_reunite i]; simp_rw [denominator,bottom_value]; split; · exact h.smooth _
   exact contDiffAt_const
lemma Seen.neg : Seen (-f) := by
    have ht:= h.scale (-1)
    rw [show -f=(-1:ℂ) • f from (neg_one_smul ..).symm]; exact ht
lemma fuse_neg : fuse R r (-f)= -fuse R r f := by rw [← neg_one_smul ℂ f,fuse_scale h,neg_one_smul]
include p in
lemma fuse_sub : Seen (f-g) ∧ fuse R r (f-g)= fuse R r f-fuse R r g := by simp_rw [sub_eq_add_neg]; rw [fuse_add h p.neg,fuse_neg p]; exact ⟨h.gathers p.neg,rfl⟩

lemma fuse_pass : Seen (Poly.pass ∘ f) ∧ fuse R r (Poly.pass ∘ f)=Poly.pass (fuse R r f) := by
   let T:= Finset.range (Fintype.card (V⊕Fin r) +1) -- edit
   let a (i:ℕ) := ((i.factorial:ℂ))⁻¹ • f^i
   have H i : Seen (a i) := (fuse_pow h i).1.scale _
   have hz : Poly.pass ∘ f=∑ i∈T,a i := by funext t; rw [Finset.sum_apply]; simp_rw [a,Pi.smul_apply, Pi.pow_apply]; rfl
   rw [hz]; refine ⟨Seen.sum _ _ (fun i _=>H i),?_⟩
   rw [fuse_sum _ _ (fun i _=> H i)]; unfold Poly.pass; exact sum_congr rfl fun i _=> (fuse_scale (fuse_pow h i).1 _).trans (congrArg (((i.factorial:ℂ))⁻¹ • ·) (fuse_pow h i).2) -- edit

include hv
omit h in
lemma fuse_leading : UnitLeading (fuse R r f) := (stamp0 f).trans (((show (fun x=> (f x).part ((M).quiet)) =ᶠ[𝓝 0] fun _=>1 from hv).eq_of_nhds : (f 0).part ((M).quiet)=1))
lemma fuse_log : Seen (connected ∘ f) ∧ fuse R r (connected ∘ f)=connected (fuse R r f) := by
   let T:= Finset.range (Fintype.card (V⊕Fin r) +1)
   let P : ℝ→δ:= 1-f; let c (i:ℕ):=(-((↑(i+1):ℂ))⁻¹:ℂ); let a (i:ℕ):= c i • P^(i+1); let u:=∑ i∈T,a i
   have h0 : Seen (1:ℝ→δ):= Seen.even 1
   have he:=fuse_sub (f:=1) h0 h
   have hp : Seen P:= he.1
   have H i : Seen (a i) := (fuse_pow hp (i+1)).1.scale _
   have hu:= Seen.sum T a (fun i _=> H i)
   have he : connected ∘ f=ᶠ[𝓝 0] u := by
      filter_upwards [hv] with x hx; rw [Function.comp_apply,log_formula hx]; unfold u; rw [Finset.sum_apply]; rfl
   rw [fuse_congr he]; refine ⟨hu.changeOf he.symm,?_⟩
   unfold u; rw [fuse_sum _ _ (fun i _=> H i), log_formula (fuse_leading hv)]; apply sum_congr rfl; intro i _; unfold a
   rw [fuse_scale (fuse_pow hp (i+1)).1, (fuse_pow hp _).2,show fuse R r P=1-fuse R r f from (fuse_sub h0 h).2.trans (congrArg (·-fuse R r f) (fuse_save _))]
lemma fuse_inverse : Seen (inverseMass ∘ f) ∧ fuse R r (inverseMass ∘ f) = inverseMass (fuse R r f) := by
    have h' := (fuse_log h hv)
    rw [show inverseMass ∘ f=Poly.pass ∘ (-(connected ∘ f)) from rfl, (fuse_pass h'.1.neg).2,fuse_neg h'.1,h'.2]; exact ⟨(fuse_pass h'.1.neg).1,rfl⟩
omit h in
lemma leads_vac : ∀ᶠ t in 𝓝 (0:ℝ),UnitLeading (denominator (f t)) := hv.mono fun t ht=> (bottom_quiet (f t)).trans ht
lemma fuse_ratio : Seen (Order.ratio ∘ f) ∧ fuse R r (Order.ratio ∘ f)=Order.ratio (fuse R r f) := by
    have he:= leads_vac hv; let g(t:ℝ):= denominator (f t)
    rw [show Order.ratio ∘ f=f * (inverseMass ∘ g) from rfl,fuse_prod h (fuse_inverse (f:=g) h.across he).1,(fuse_inverse (f:=g) h.across he).2, ← show denominator (fuse R r f)= fuse R r g from absorb f]; exact ⟨h.product (fuse_inverse (f:=g) h.across he).1,rfl⟩
lemma fuse_mark : Seen (logMarked ∘ f) ∧ fuse R r (logMarked ∘ f)=logMarked (fuse R r f) := by
   let g:= Order.ratio ∘ f
   have he:= (fuse_ratio h hv)
   have hx : ∀ᶠ x in 𝓝 0,UnitLeading (g x) := hv.mono (fun _ hp=> ratio_quiet hp)
   have hy := fuse_log he.1 hx; exact ⟨hy.1, hy.2.trans (congrArg connected he.2)⟩
lemma fuse_vac : Seen (logVac ∘ f) ∧ fuse R r (logVac ∘ f)=logVac (fuse R r f) := by
   have he:= leads_vac hv; have hx:= fuse_log h.across he; exact ⟨hx.1,hx.2.trans (congrArg connected (absorb f).symm)⟩
end YM.Comparison.RG02.Moving.Shift
