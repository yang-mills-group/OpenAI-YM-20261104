import YM.MSbar.Dim.Tower

/-! Bilinear trace, linear jet. Spacetime hat polarizations vary over the full fiber. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function MeasureTheory Finset
open scoped Topology ContDiff BigOperators Classical
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
-- fiber variation along arbitrary spectator list. If scalar tag, don't use its vector.
def One (p:Prop)(f:X→ℂ) : Prop := if p then ∃ F:X→ₗ[ℝ]ℂ, ∀ x,f x=F x else ∃ c:ℂ,∀ x,f x=c
def Two (p:Prop)(f:X→ℂ) : Prop := if p then ∃ F:X→ₗ[ℝ]X→ₗ[ℝ]ℂ, ∀ x,f x=F x x else ∃ c:ℂ,∀ x,f x=c
variable {f g : X→ℂ} {p : Prop}
namespace One
lemma add (hf : One p f)(hg: One p g): One p (f+g):=by
   unfold One at *; split_ifs at * with h
   · obtain ⟨F,hF⟩:=hf;obtain ⟨G,hG⟩:=hg; exact ⟨F+G,fun x=> by simp [hF x,hG x]⟩
   obtain ⟨a,ha⟩:=hf; obtain ⟨b,hb⟩:=hg; exact ⟨a+b,fun x=> congr_arg₂ (·+·) (ha x) (hb x)⟩
lemma zero : One p (0:X→ℂ):=by unfold One; split_ifs <;> exact ⟨0,fun _=>rfl⟩
lemma sum {ι:Type*}{P:Finset ι}{f:ι→X→ℂ}(he:∀ i∈P,One p (f i)): One p (∑ i∈P,f i):=by induction P using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i s h ih=> rw [Finset.sum_insert h]; exact (he i (Finset.mem_insert_self ..)).add (ih fun j hj=> he _ (Finset.mem_insert_of_mem hj))
lemma scale (c:ℂ)(hf:One p f): One p (c • f):=by
   unfold One at *; split_ifs at * with h
   · obtain ⟨F,hF⟩:=hf; exact ⟨c • F,fun x=>by simp [hF x]⟩
   obtain ⟨u,hU⟩:=hf; exact ⟨c*u,fun x=>by simp [hU x]⟩
lemma neg (hf:One p f): One p (-f):=by simpa using hf.scale (-1:ℂ)
lemma sub (hf:One p f)(hg:One p g): One p (f-g):=by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma compose (hf:One p f)(L:Y→ₗ[ℝ]X): One p (f ∘ L):=by
   unfold One at *; split_ifs at * with h
   · obtain ⟨A,hA⟩:=hf; exact ⟨A.comp L,fun x=>hA _⟩
   obtain ⟨c,hc⟩:=hf; exact ⟨_,fun x=>hc (L x)⟩
lemma product (hf:One p f)(hg:One p g): Two p (f*g):=by
   unfold One at *; unfold Two; split_ifs at * with h
   · obtain ⟨A,hA⟩:=hf; obtain ⟨B,hB⟩:=hg; exact ⟨((LinearMap.mul ℝ ℂ).comp A).compl₂ B, fun x=>by simp [hA x,hB x]⟩
   obtain ⟨a,ha⟩:=hf; obtain ⟨b,hb⟩:=hg; exact ⟨a*b,fun x=>by simp [ha x,hb x]⟩
end One
namespace Two
lemma add (hf : Two p f)(hg: Two p g): Two p (f+g):=by
   unfold Two at *; split_ifs at * with h
   · obtain ⟨F,hF⟩:=hf;obtain ⟨G,hG⟩:=hg; exact ⟨F+G,fun x=> by simp [hF x,hG x]⟩
   obtain ⟨a,ha⟩:=hf; obtain ⟨b,hb⟩:=hg; exact ⟨a+b,fun x=> congr_arg₂ (·+·) (ha x) (hb x)⟩
lemma zero : Two p (0:X→ℂ):=by unfold Two; split_ifs <;> exact ⟨0,fun _=>rfl⟩
lemma sum {ι:Type*}{P:Finset ι}{f:ι→X→ℂ}(he:∀ i∈P,Two p (f i)): Two p (∑ i∈P,f i):=by induction P using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i s h ih=> rw [Finset.sum_insert h]; exact (he i (Finset.mem_insert_self ..)).add (ih fun j hj=> he _ (Finset.mem_insert_of_mem hj))
lemma scale (c:ℂ)(hf:Two p f): Two p (c • f):=by
   unfold Two at *; split_ifs at * with h
   · obtain ⟨F,hF⟩:=hf; exact ⟨c • F,fun x=>by simp [hF x]⟩
   obtain ⟨u,hU⟩:=hf; exact ⟨c*u,fun x=>by simp [hU x]⟩
lemma neg (hf:Two p f): Two p (-f):=by simpa using hf.scale (-1:ℂ)
lemma sub (hf:Two p f)(hg:Two p g): Two p (f-g):=by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma compose (hf:Two p f)(L:Y→ₗ[ℝ]X): Two p (f ∘ L):=by
   unfold Two at *; split_ifs at * with h
   · obtain ⟨A,hA⟩:=hf; exact ⟨(A.comp L).compl₂ L,fun x=>hA _⟩
   obtain ⟨c,hc⟩:=hf; exact ⟨_,fun x=>hc (L x)⟩
end Two
end YM.MSbar.Dim
