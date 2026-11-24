import YM.WilsonCoeffUV.FieldRead.Label

/-! Engineering and root stamp; off-shell calibration, signed
symmetry preserving. Pol(B) with addressed letters. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider Fountain
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m n p e:ℕ}{A C s t :ℝ}
variable (F: Labels.Frame G h)
abbrev Alma (F: Labels.Frame G h) := {i:F.Index× Embroider.Spiral h // (F.grades i.1).1+rankS i.2≤ h}
def sheet (i:Alma F):= i.val.1
def notar (i:Alma F):= i.val.2
def weave (i:Alma F):= (F.grades (sheet F i)).1
def valence (i:Alma F):=(F.grades (sheet F i)).2
def weight (i:Alma F):= weave F i+rankS (notar F i)
lemma weigh_cap (i: Alma F):weight F i≤h:= i.property
lemma value_le (i:F.Index): (F.grades i).2 ≤ h:=by
    have he : (F.basis i).val ≠ 0:= fun t=> F.basis.ne_zero i (Subtype.ext t)
    obtain ⟨m,hm⟩ := MvPolynomial.support_nonempty.mpr he
    have ht := (pure_grade _ _).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hm)
    have hx := power_le (G:=G) m; rw [ht] at hx; exact le_trans hx ((MvPolynomial.mem_restrictSupport_iff ℂ).mp (show (F.basis i).val∈limited G h from (F.basis i).property.1) hm)
lemma valence_cap (i:Alma F):valence F i≤ h:= value_le F _
lemma ticket_grade (x: Label G h) (i:F.Index)(n l:ℕ): F.coords (gradePart (n,l) x) i= if (n,l)=F.grades i then F.coords x i else 0:=by
    split
    next H=>
       calc
           _=∑ j:F.Index, if (n,l)=F.grades j then F.coords ((F.basis.repr x j) • F.basis j) i else 0:= by
               conv_lhs=> rw [← F.basis.sum_repr x,map_sum,map_sum,Finset.sum_apply]
               apply Finset.sum_congr rfl; intro j _; split
               next e=> rw [e,map_smul,gradePart_self _ _ (F.pure j)]
               next e => rw [LinearMap.map_smul,gradePart_zero _ _ _ e (F.pure j)]; simp
           _ = _:= by
               rw [Finset.sum_eq_single i]; rw [if_pos H,map_smul,F.coords_basis]; simp; rfl
               intro b _ hb; rw [map_smul,F.coords_basis,Pi.smul_apply,Pi.single_eq_of_ne hb.symm]; simp
               simp
    next e=> exact F.power_coefficient _ e (gradePart_mem ..)

abbrev Alight (F:Frame G h) := Alma F→ℝ
def bleached (F:Frame G h) (v:Ortho) (i j:F.Index) := (F.act v (Pi.single j 1) i).re
lemma bleach_even (s:Ortho)(i j:F.Index): F.act s (Pi.single j 1) i=(bleached F s i j:ℂ):=by
   unfold bleached; rw [← F.coords_basis, Frame.act_coords]
   let X:=Labels.tensor s (F.basis j); have hx: realBar X=X:=by simp [X, F.realForm]
   have h : star (F.coords X i)= F.coords X i:= by rw [←Frame.conj_basis,F.coords.symm_apply_apply,hx]
   have ht: (F.coords X i).im=0:=by have hh:= congr_arg Complex.im h; simp at hh; linarith
   exact Complex.ext rfl (by simpa using ht)
lemma bleach_sparse (s:Ortho)(i j:F.Index)(h:F.grades j≠F.grades i): bleached F s i j=0:=by
   have he:F.act s (Pi.single j 1) i=0:=by
       rw [← F.coords_basis,F.act_coords]; apply F.power_coefficient i h; have he := F.pure j
       nth_rw 1 [← gradePart_self _ _ he]; rw [← gradePart_turn]; exact gradePart_mem ..
   unfold bleached; rw [he]; rfl
lemma pollenC (s:Ortho)(i:F.Index)(X:F.Coeff): F.act s X i=∑ b:F.Index,(bleached F s i b:ℂ)*X b:=by
   conv_lhs=>rw [show X=∑ b:F.Index,X b • Pi.single b 1 from funext fun k=> by simp [Pi.single_apply],map_sum,Finset.sum_apply]
   apply Finset.sum_congr rfl; intro b _; rw [map_smul,Pi.smul_apply,bleach_even]; exact mul_comm ..
lemma pulp (s:Ortho)(i:F.Index)(X:F.Coeff): (F.act s X i).re= ∑ b,bleached F s i b*(X b).re:=by rw [pollenC F]; simp

def blueIn (s:Signed) (i j:Alma F) : ℝ:= if spindle s (notar F j) =notar F i then hue s (notar F j).val*bleached F s.ortho (sheet F i) (sheet F j) else 0
lemma mien (s:Signed)(i j:Alma F)(H:blueIn F s i j≠0): (weight F i,valence F i)=(weight F j,valence F j) ∧ spindle s (notar F j)=notar F i:=by
    have hv : spindle s (notar F j)=notar F i:= by by_contra h; apply H; unfold blueIn; rw [if_neg h]
    have ht : F.grades (sheet F j)=F.grades (sheet F i):= by by_contra h; apply H; simp [blueIn,hv, bleach_sparse F _ _ _ h]
    unfold weight weave valence; rw [ht,←hv, Embroider.spun_card]; exact ⟨rfl,rfl⟩

/-! Reindex over `i` held grade. -/
theorem reducing (s:Signed)(f:F.Index)(u:Embroider.Spiral h)(n:ℕ)(H: (F.grades f).1+rankS u≤h)(_he:(F.grades f).1=n) (b:Alma F)(e:b.val=(f,spindle s u))(Q:Alight F)(g:F.Index→ℝ)(hp:∀ i:Alma F,notar F i=u → F.grades (sheet F i)=F.grades f → Q i=g (sheet F i)): (∑ i,blueIn F s b i*Q i) = hue s u.val*(∑ i:F.Index,bleached F s.ortho f i*g i):=by
    subst n
    let X:Finset (Alma F):= Finset.univ.filter fun i=> notar F i=u ∧ F.grades (sheet F i)=F.grades f
    let Y:= Finset.univ.filter fun j=> F.grades j=F.grades f
    rw [Finset.mul_sum,← Finset.sum_subset (Finset.subset_univ X),← Finset.sum_subset (s₁:=Y) (Finset.subset_univ _)]
    · refine Finset.sum_bij (fun i _=> sheet F i) ?_ ?_ ?_ ?_
      · exact fun i hx=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2.2⟩
      · intro i hi j hj ht; exact Subtype.ext (Prod.ext ht (((Finset.mem_filter.mp hi).2.1).trans ((Finset.mem_filter.mp hj).2.1).symm))
      · intro i hi; have hi:= (Finset.mem_filter.mp hi).2; have ha: (F.grades i).1+rankS u≤ h:=hi.symm ▸ H
        exact ⟨⟨(i,u),ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,hi⟩,rfl⟩
      intro i hi; obtain ⟨hv,hh⟩:= (Finset.mem_filter.mp hi).2; unfold blueIn; rw [hp i hv hh,hv,show sheet F b=f from congr_arg Prod.fst e,if_pos (show spindle s u=notar F b from Eq.symm (congr_arg Prod.snd e))]; ring
    · intro i hi hu; have ht : F.grades i≠F.grades f:=fun h=>hu (Finset.mem_filter.mpr ⟨hi,h⟩); rw [bleach_sparse F _ _ _ ht]; ring
    intro i hi hx; unfold blueIn; rw [show notar F b=spindle s u from congr_arg Prod.snd e]; split
    next h=> have he:= congr_arg (spindle s⁻¹) h; simp_rw [unspindle] at he; rw [show sheet F b=f from congr_arg Prod.fst e,bleach_sparse F _ _ _ (fun b=>hx (Finset.mem_filter.mpr ⟨hi,he,b⟩))]; ring
    next h=> simp

lemma drift (s:Signed)(i:Alma F): ∃ (u:Embroider.Spiral h), (F.grades (sheet F i)).1+ rankS u≤h ∧ i.val=(sheet F i,spindle s u):=by
   let u:=spindle s⁻¹ (notar F i); refine ⟨u,?_ ,?_⟩
   · unfold u; rw [spun_card]; exact weigh_cap ..
   unfold u; rw [show spindle s (spindle s⁻¹ (notar F i))=notar F i from inv_inv s ▸ unspindle s⁻¹ _]; rfl
end YM.WilsonCoeffUV.Cosmos
