import YM.RegulatorIR.Geometry.Fields
import YM.PertExtension.OrbFlat

/-! Terminal slice allows locating the top flat orbit even if pure gauge links.
Also pack integrable densities, not only continuous ones. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry.End
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {f:Side}{G:Gauge}

abbrev last (G:Gauge)(f:Side):=shellMeasure G (Cotree f)
def punch (G:Gauge) (f:Side): spins G f≃ᵐ ((Orb.Trees f→G.El)×(Cotree f→G.El)):=MeasurableEquiv.piEquivPiSubtypeProd _ _
lemma pulse : MeasurePreserving (punch G f) (spinsMeasure G f) ((shellMeasure G (Trees f)).prod (last G f)):= measurePreserving_piEquivPiSubtypeProd (fun _=>G.probHaar) Branch
lemma punched (x : Trees f→G.El)(y:Cotree f→G.El): (punch G f).symm (x,y) = splitLink x y:=by
 ext1 i; by_cases he:Branch i
 · exact (congr_fun (congr_arg Prod.fst ((punch G f).apply_symm_apply (x,y))) ⟨i,he⟩).trans (by unfold splitLink;rw [dif_pos he])
 exact (congr_fun (congr_arg Prod.snd ((punch G f).apply_symm_apply (x,y))) ⟨i,he⟩).trans (by unfold splitLink;rw [dif_neg he])
lemma fixed (h:Even f.val)(b:Trees f→G.El)(x:Cotree f→G.El): goat (frame b) (splitLink b x)=splitLink 1 (fresh b x):= by
 have ht := Orb.alignment h b x
 have he: orbLift (goat (frame b) (splitLink b x))=orbLift (splitLink 1 (fresh b x)):=by rw [goat_lift];exact ht; exact frame_neg _
 ext1 i; rw [← lift_at (goat (frame b) (splitLink b x)) i, ← lift_at (splitLink 1 (fresh b x)) i]; exact congr_fun he _

def rebase (b:Trees f→G.El): (Cotree f→ G.El)≃ᵐ (Cotree f→G.El) where
 toFun:=fresh b
 invFun y i := (frame b i.val.val.1)⁻¹*y i* frame b (i.val.val.1+step i.val.val.2)
 left_inv:= by intro y;ext1 i; simp only [fresh];group
 right_inv:= by intro y;ext1 i; simp only [fresh];group
 measurable_toFun:=fresh_meas G b
 measurable_invFun:=by simp only [Equiv.coe_fn_symm_mk];fun_prop
lemma torque (b:Trees f→G.El): MeasurePreserving (rebase b) (last G f) (last G f) := Orb.rotated G b

theorem finish (D:spins G f→ℝ)(h:Integrable D (spinsMeasure G f))(he:Even f.val) (H:∀ k:Site f→G.El, compatible k→ ∀ U,D (goat k U)=D U) : (∫ x,D x ∂spinsMeasure G f)=∫ y,D (splitLink 1 y) ∂last G f:=by
 let P:=punch G f
 have ht:= pulse (f:=f) (G:=G)
 have hx:Integrable (fun x=> D ((punch G f).symm x)) ((shellMeasure G (Trees f)).prod (last G f)):= (ht.symm.integrable_comp_emb P.symm.measurableEmbedding).mpr h
 rw [← ht.symm.integral_comp' D,integral_prod _ hx]
 have hp b: (∫ x,D ((punch G f).symm (b,x)) ∂last G f)=∫ x,D (splitLink 1 x) ∂last G f:=by
   have hz x : D ((punch G f).symm (b,x))= D (splitLink 1 (fresh b x)):=by rw [punched,← fixed he,H _ (frame_neg _)]
   simp_rw [hz]; exact (torque b).integral_comp' (fun x=>D (splitLink 1 x))
 change (∫ b,∫ x,D ((punch G f).symm (b,x)) ∂last G f ∂shellMeasure G (Trees f))=_
 simp_rw [hp]; simp

lemma goat_flat (U:spins G f)(hp:Even f.val)(h: energy (orbLift U)=0): ∃ k:Site f→ G.El, compatible k ∧ goat k U=1:=by
 obtain ⟨⟨p,q⟩,rfl⟩:= (punch G f).symm.surjective U
 rw [punched] at *
 refine ⟨frame p,frame_neg _,?_⟩
 have he:energy (orbLift (goat (frame p) (splitLink p q)))=0 :=by rw [goat_lift _ _ (frame_neg _)]; unfold energy; simp_rw [face_gauge, G.price_conj]; exact h
 rw [fixed hp p q] at he ⊢; rw [flat_unique hp he]; ext1 i; unfold splitLink;split_ifs <;> rfl
end YM.RegulatorIR.Geometry.End
