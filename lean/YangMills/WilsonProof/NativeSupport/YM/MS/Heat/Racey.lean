import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.GroupX
import Mathlib.MeasureTheory.Group.Integral
/-!
# Commuting point-integrals through linear operations

Integrability on all necessary contexts but no topology required on `Row`.
Use finite components across $Δ$ crossings, stable through truncations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
variable {P I A:Type} [AddCommGroup P] [Fintype A]{p: Sector A}{K L:Flux A P ℂ}{F H: Row A P ℂ}
-- encode Point Cette locally finite evaluation tests. Maps `P` generic. Facilitates derivative smooth too.
variable {D X Y:Type} {J:Type} [MeasurableSpace I] (μ:Measure I)
-- sensible L from point-linear space
structure Sensible (L:(X→ℂ)→ (Y→ℂ)): Prop where
    reaches (i:Y): (fun f=> L f i)∈ Submodule.span ℂ {E|∃ j:X,E=fun f=> f j}
section B
open Submodule
abbrev Centre (X:Type):= Submodule.span ℂ {E :(X→ℂ)→ℂ|∃ j:X,E=fun f=> f j}
lemma centroid (i:X): (fun f=> f i)∈Centre X:= by exact subset_span (mem_setOf.mpr ⟨i,rfl⟩)
lemma cent_add (f g:(X→ℂ)→ℂ) (h:f∈Centre X)(ht:g∈Centre X): (fun p=>f p+g p)∈Centre X:= h |> (Centre X).add_mem <| ht
lemma cent_sum (J: Finset Y)(f:Y→ (X→ℂ)→ℂ)(h:∀ i∈J,f i∈Centre X): (fun x=>∑ i∈J,f i x)∈Centre X:= by rw [show (fun x=>_)=∑ i∈J,f i from funext fun x=> Eq.symm (Finset.sum_apply ..)]; exact sum_mem h
lemma cent_scale (c:ℂ)(f:(X→ℂ)→ℂ)(h:f∈Centre X): (fun x=>c*f x)∈Centre X:= (Centre X).smul_mem c h
lemma cent_arguments {U : (X→ℂ)→ℂ} (H:U∈Centre X){f:I→ X→ℂ}(hx:∀ i, Integrable (fun x=>f x i) μ) : Integrable (fun x=>U (f x)) μ ∧ (∫ x,U (f x) ∂μ)=U (fun i=>∫ x,f x i ∂μ):=by
    refine span_induction (x:=U) (p:=fun U _=>Integrable (fun x=>U (f x)) μ ∧ (∫ x,U (f x) ∂μ)=U (fun i=>∫ x,f x i ∂μ)) ?_ (by simp) ?_ ?_ H
    · rintro x ⟨i,rfl⟩; exact ⟨hx i,rfl⟩
    · intro i j a b hp hk; exact ⟨hp.1.add hk.1,by simp_rw [Pi.add_apply,integral_add hp.1 hk.1,hp.2,hk.2]⟩
    intro c U h hx; exact ⟨hx.1.const_mul c,by simp_rw [Pi.smul_apply,integral_smul,hx.2]⟩
omit [Fintype A] in
lemma cent_gather (p:Sector A)(w:Legs A)(F:(X→ℂ)→ Shared A ℂ)(h:∀ i j,Split i j w→ (fun f=> F f i j)∈Centre X): (fun f=> scatter p w (F f))∈Centre X:= by
    induction w generalizing F with | nil=>exact h _ _ .nil| cons a w ih=> exact ih _ (fun i j h'=> cent_add _ _ (h _ _ h'.left) (cent_scale _ _ (h _ _ h'.right)))
end B
-- conflicts binder A duplicate remove
lemma sense_atRight (K:Flux A P ℂ) (F:Row A P ℂ) : Sensible (tree p K F):=by
   refine ⟨fun k=> cent_gather (field p) _ _ (fun i j h=>?_)⟩; unfold attaches; dsimp only; refine cent_sum _ _ (fun a _=>cent_sum _ _ (fun q _=>cent_add _ _ ?_ ?_)) <;> exact (by simp_rw [← mul_assoc]; apply cent_scale _ _ (centroid _))
lemma sense_atLeft (K:Flux A P ℂ)(F:Row A P ℂ) : Sensible (fun H=>tree p K H F):= by
   refine ⟨fun k=> cent_gather (field p) _ _ (fun i j h=> ?_)⟩; unfold attaches; dsimp only; refine cent_sum _ _ (fun a _=>cent_sum _ _ (fun q _=>cent_add _ _ ?_ ?_)) <;> (simp_rw [mul_comm _ (F _),← mul_assoc]; exact (cent_scale _ _ (centroid _)))
lemma sense_trc (K:Flux A P ℂ)(q:P): Sensible (trc K q):= by refine ⟨fun i=>?_⟩; simp_rw [at_trc]; exact cent_sum _ _ (fun i _=> cent_sum _ _ (fun j _=> cent_scale _ _ (centroid _)))
-- raise part
omit [AddCommGroup P] in
lemma sense_Q (Z:Charge p P ℂ): Sensible Z.raise:= by
   refine ⟨fun i=>?_⟩
   have he (w:Legs (Mode A P))(K:Row A P ℂ→ Slash A P ℂ)(h:∀ i j l, i++(j::l)=w → (fun f=> K f i j l)∈ Centre (Legs (Mode A P))): (fun f=> visit true p w (K f))∈ Centre (Legs (Mode A P)):= by
       induction w generalizing K with | nil=> exact (Centre _).zero_mem| cons i w ih=> exact cent_add _ _ (h [] i w rfl) (cent_scale _ _ (ih _ (fun a b l H=> h (i::a) b l (by simp [H]))))
   simp_rw [visit_Z]; exact he _ _ (fun l k i h=> cent_sum _ _ (fun i _=> cent_scale _ _ (centroid _)))
end YM.MS.Heat
