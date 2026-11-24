import YM.Qlocal.Canopy.Button
/- # Reading actual merged occupations of all perturbative terms.
  Includes charging (finite poles), projection at held-root masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy
open Function Finset Filter Marker Multi Merge Switch
open Comparison.RG02.Order Comparison.RG02.Cumulants Comparison.RG02.Assembly
open PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP
open AllOrder.Response Extra.Trajectories Next.SectorChange
open scoped Topology ContDiff BigOperators Classical
variable {ι σ : Type} {V:Type} [DecidableEq V] {R:Census V} (K:ι→Multi.Hot R)
namespace Button
open Bind PositionX.Jet
variable {A P:Finset ι}
abbrev peg (i:ι):= (K i).val
abbrev plant (i:ι): Poly R:= Poly.send (peg K i) 1
lemma clicked i: plant K i * plant K i=0:= send_noProd (fun ⟨p,h⟩ => (K i).property.ne_empty (disjoint_self.mp h.1)) _ _
abbrev pose (u:Finset ι): Poly R:= ∏ j∈u, plant K j
-- to detect an admissible interaction (no dependence on width amplitudes)
def Ideal (P:Finset ι): Prop:= Extra.Trajectories.Fits (peg K) P
lemma meetsP (K:ι→Multi.Hot R)(h:Ideal K P)(he:A ⊆ P): Ideal K A:= Fits.subset _ h he
lemma plantBase : Ideal K ∅:= fits_empty _
abbrev pin (P:Finset ι) (h:Ideal K P):= Extra.Trajectories.unionTag (peg K) P h
lemma spar (h:Ideal K P): pose K P= Poly.send (pin K P h) 1:=by unfold pose plant; rw [tagged_prod _ _ h,prod_const_one];-- rfl
lemma spacer (h:¬Ideal K P): pose K P=0:=by by_contra h'; exact h (fits_of_tagged_prod (peg K) h')
lemma burgeon (h:Ideal K P): pose K P≠0:=fun H=> (one_ne_zero (α:=ℂ)) (by simpa [spar _ h] using congr_arg (fun b:Poly R=>b.part (pin K P h)) H)
lemma report (h:Ideal K P)(i:ι)(hp:i∈P){q:V}: q∈ (K i).val.val → q∈ (pin K P h).val:= fun hx=> mem_biUnion.mpr ⟨i,hp,hx⟩
lemma spring (h:Ideal K P)(hp:P.Nonempty): ((pin K P h)).val.Nonempty:= by obtain ⟨p,hp⟩:=hp; exact (K p).property.mono (fun x hx=> report K h p hp hx) -- hx not explicit?
def flush (P:Finset ι)(h:Ideal K P)(hp:P.Nonempty): Multi.Hot R:= ⟨pin K P h,spring K h hp⟩
-- capt.F: price traveling Lens.
lemma bending (h:Ideal K P)(he:A ⊆ P)(h₁ h₂:Ideal K A): (pin K A h₁=pin K P h) ↔ A=P:= by
 refine ⟨fun hh=>Finset.Subset.antisymm he ?_,?_⟩
 · intro i hi; obtain ⟨a,ha⟩:= (K i|>.property); have hz : a∈(pin K A h₂).val:= by rw [hh]; exact report K h i hi ha
   obtain ⟨b,hb,hb'⟩:= mem_biUnion.mp hz; have he' : b=i:= by by_contra hq; exact Finset.disjoint_left.mp ((show Fits (peg K) P from h).1 (he hb) hi hq) hb' ha
   rwa [← he']
 intro he; subst P; rfl
variable [Fintype ι]
def sput (K:ι→Poly R) (s:Finset ι) (u:Word ℝ): PTable R:= realCurve R u * (PowerSeries.C (∏ i∈s,K i))
lemma scattered (K:ι→Poly R) (s:Finset ι) (u:Word ℝ)(i:ℕ): PowerSeries.coeff i (sput K s u)=(↑(u i):ℂ)• (∏ j∈s,K j):= by rw [sput, PowerSeries.coeff_mul_C,realCoeff,Poly.product_bead] -- Fintype unneces.
lemma swept (K:ι→Poly R) (O:Book ι): scribe K O= ∑ j:Finset ι, sput K j (swap O j):= by ext1 i; rw [written,map_sum]; simp_rw [scattered]; exact mapScores_apply _ _
lemma dyes (h:Ideal K P)(hz:P.Nonempty)(v:Word ℝ): sput (plant K) P v= Glyph.wire (flush K P h hz) v:=by
 ext i s; rw [Bind.Glyph.wired,scattered]; change ((_ • pose K P):Poly R).part s=_; rw [spar K h,Poly.part_smul]; have hx : s= (flush K P h hz).val ↔ s=pin K P h:= Iff.rfl; simp only [hx,Poly.part_send,flush]; split_ifs <;> simp
lemma dies (h:¬Ideal K P)(v:Word ℝ): sput (plant K) P v=0:= by ext1 i; rw [scattered,map_zero]; change _ • pose K P=0; rw [spacer K h,smul_zero]
lemma voiced {K:ι→Poly R}(v:Word ℝ): sput K ∅ v=realCurve R v:= by unfold sput; rw [prod_empty,map_one,mul_one]
abbrev maps (B:Score ι):= mapScores R (plant K) B
lemma by_key (O:Book ι) (hv:Ideal K univ) (i) : ((PowerSeries.coeff i) (scribe (plant K) O)).part (pin K univ hv)= (O i univ:ℂ):=by
 rw [written,mapScores_apply,Poly.part_sum,sum_eq_single univ, Poly.part_smul, show (∏ j,plant K j)=_ from spar K hv, Poly.part_send, if_pos rfl,mul_one] -- rw pose vs display
 · intro A _ ha; let h:= meetsP K hv (subset_univ A); rw [Poly.part_smul,show (∏ i∈A, plant K i)=_ from spar K h, Poly.part_send,if_neg (fun he=> ha ((bending K hv (subset_univ A) h h).1 he.symm)),mul_zero]
 simp
end Button
end YM.Qlocal.Canopy
