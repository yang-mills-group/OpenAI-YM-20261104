import YM.SchemeConversionRG11.FirstW.Lien.Hues
/-! Projecting only as far as warranted by convergence. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G:Gauge} {F : Labels.Frames G}
-- linear selector
lemma fingers {U V:Type*}[AddCommGroup U][AddCommGroup V][Module ℝ U][Module ℝ V] (L:U→ₗ[ℝ]V) (Z D P:Submodule ℝ V)
   (hZ:Z≤D)(hD:D≤P)(hP:∀ v:V,v∈ D → ∃ u:U,v-L u∈Z): ∃ H: V→ₗ[ℝ]U,
     (∀ v:V,v∈Z → H v=0) ∧ (∀ v:V,v∈D → v-L (H v)∈Z) ∧ ∀ v:V,L (H v)∈P := by
  let Q:=Z.mkQ; let S:= Q ∘ₗ D.subtype; let T:= Q.comp L
  obtain ⟨R,hR⟩:= choosingR T; obtain ⟨A,hA⟩:= choosingR S
  let H:= R.comp (S.comp (A.comp Q)); have he(v:V): H v= R (S (A (Q v))):=rfl
  have hu (q : D): ∃ u:U,S q=T u:=by obtain ⟨u,H⟩:= hP q.val q.property; refine ⟨u,?_⟩; apply sub_eq_zero.mp; change Q q.val - Q (L u)=0; rw [← map_sub]; exact Submodule.Quotient.mk_eq_zero Z|>.2 H
  have hs (v:V): L (H v)-(A (Q v)).val∈Z:=by
    rw [← Submodule.Quotient.mk_eq_zero]; change Q _=0; rw [map_sub,he]; apply sub_eq_zero.mpr; change T _=S _; obtain ⟨u,h⟩:=hu (A (Q v)); rw [h,hR]
  refine ⟨H,fun v hv=> ?_,fun v hv=>?_,fun v=>?_⟩
  · rw [he,show Q v=0 from (Submodule.Quotient.mk_eq_zero Z).mpr hv,map_zero,map_zero,map_zero]
  · rw [← Submodule.Quotient.mk_eq_zero]; change Q _=0; rw [map_sub,he]; apply sub_eq_zero.mpr; symm; let q:D:=⟨_,hv⟩; change T (R (S (A (S q))))= S q; rw [hA]; obtain ⟨u,h⟩:=hu q; rw [h,hR]
  have hk := D.add_mem (hZ (hs v)) (A (Q v)).property; rw [sub_add_cancel] at hk; exact hD hk
def Summit {U V:Type*}[AddCommGroup U][AddCommGroup V][Module ℝ U][Module ℝ V] (L:U→ₗ[ℝ]V)(Z D P:Submodule ℝ V):Prop:=∃ H: V→ₗ[ℝ]U,(∀ v:V,v∈Z → H v=0) ∧ (∀ v:V,v∈D → v-L (H v)∈Z) ∧ ∀ v:V,L (H v)∈P
lemma finds {U V:Type*}[AddCommGroup U][AddCommGroup V][Module ℝ U][Module ℝ V] (L:U→ₗ[ℝ]V)(Z D P:Submodule ℝ V) (hZ:Z≤D)(hD:D≤P)(hP:∀ v:V,v∈ D → ∃ u:U,v-L u∈Z): Summit L Z D P:=fingers L Z D P hZ hD hP
lemma coverPk (i:ℕ)(he:i≤4) (F : Labels.Frames G): Summit (V:=Bond F) (U:=Pack F) (glyph F) (mask F (i+1)) (mask F i ⊓ hum F (i+1)) (mask F i) := by
 refine finds _ _ _ _ mask_more inf_le_left ?_
 intro v hv; exact mask_precise i he v hv

variable {S : Itinerary}
def paidC (S:Itinerary) (k : ℕ) (w : ℕ→ Bond F) := ∀ i < k,∀ s:CheckQ F,s.i+s.j=i → Helen (fun j=> ((S.gap j ^(4-i))⁻¹:ℝ) • rate s (w j))
-- upper leakage h (only prefix through 4)
def fitsM (S:Itinerary)(w:ℕ→Bond F):=∀ q:CheckQ F,q.i+q.j≤4 → Tendsto (fun j=> S.gap j • rate q (w j)) atTop (𝓝 0)
def kissC (S:Itinerary)(w:ℕ→Bond F):=∀ i ≤ 4,∀ s:CheckQ F,s.i+s.j=i → quietly s.a.val → Helen (fun j=> ((S.gap j ^ (4-i))⁻¹:ℝ) • rate s (w j))
-- charge lemmas transfer along kernels. budget n below tested gradient order.
lemma higherH {r:ℕ→ℂ}{a b:ℕ}(h:a≤b)(ht:Helen (fun j=>(S.gap j ^ b)⁻¹ • r j)): Helen (fun j=>(S.gap j ^ a)⁻¹ • r j) := by
 obtain ⟨u,hp⟩:=ht
 have hh (j:ℕ): S.gap j^(b-a) * (S.gap j ^ b)⁻¹ = (S.gap j ^ a)⁻¹:=by
   rw [show S.gap j ^ b=S.gap j ^(b-a)* S.gap j^a from by rw [← pow_add,Nat.sub_add_cancel h],mul_inv,mul_inv_cancel_left₀ (pow_ne_zero _ (S.positive j).ne')]
 exact ⟨_,((S.cutoff.pow (b-a)).smul hp).congr fun i=>by rw [smul_smul,hh]⟩
end YM.RG11.FirstW
