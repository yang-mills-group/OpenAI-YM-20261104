import YM.SchemeConversionRG11.FirstW.Due.Balcony
import YM.SchemeConversionRG11.Field.Horizon
import YangMills.WilsonProof.NativeSupport.YM.Extra.WEAK_SCALING_ACTLAW.Color
/-! One-open correction killed, unit counterterm lives in legitimate Buffer. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD SchemeConversionRG11.Horizon MvPolynomial Position
open scoped BigOperators Classical
variable {G : Gauge} {d : ℕ} {n : Side} (F : Labels.Frames G)
def torT (n : Side) (d : ℕ) (h : ℝ) (o : Site n) (i : Who G d) := river h i.val o
lemma one_open (p:E F d) (o:Site n) (h : ℝ) (hg : G.Simple) (A:FullT G n) (T : Sky G (Per n)) (ht : ∀ u: G.El,∀ A B C,T (putting u A) (putting u B) (putting u C)=T A B C): zinc (torT n d h o) h o T (cloak F p) A=0 := by
 let K:=torT (G:=G) n d h o
 let Z:FullT G n→ₗ[ℝ]ℂ:=∑ a:Who G d,∑ b:Who G d,loot (cloak F p) a b • Complex.ofRealCLM.toLinearMap.comp (sectorA K h o T a b)
 have hp (A : FullT G n): Z A = zinc K h o T (cloak F p) A := by unfold Z; simp only [LinearMap.sum_apply];rfl
 have he (u:G.El) (A:FullT G n): Z (putting u A)=Z A := by
   rw [hp,hp]; let L:=paintL d u; let Q:=tint_pl d u o h; exact (tint_zinc K h o T (cloak F p) _ (putting u) L Q (fun x=>(tint F u x p).symm) (TintK _ L o h Q (color_branch u)) (ht u) A).symm
 let g (i:Edge (Site n)): G.Color →ₗ[ℝ] FullT G n:= LinearMap.single ℝ (fun _ : Edge (Site n)=> G.Color) i -- check
 have eh (i: Edge (Site n)) (v : G.Color) : Z (g i v)=0:= Extra.WeakScaling.Color.linear_invariant hg (Z.comp (g i)) (fun u x=>by
    rw [LinearMap.comp_apply,LinearMap.comp_apply]; rw [show g i (G.adjoint u x)=putting u (g i x) from funext fun l=>by simp only [g,LinearMap.single_apply, putting_node]; by_cases h:i=l <;> simp [h,Ne.symm]]; exact he u _) v
 rw [show torT (G:=G) n d h o=K from rfl,←hp,beads A,map_sum,Finset.sum_eq_zero]; intro i _; rw [show snow i=g i.fst (unitColor G i.2) from funext fun l=>by simp only [snow, pinched, g,LinearMap.single_apply,Pi.single_apply],map_smul,eh, smul_zero] -- vacuum
lemma tangI (a b c : Who G 6) (p:E F 6) (j : ℕ) (hj:j<6) (H : p∈lower F j 6): root3 (cloak F p) a b c=0 := by
 rw [←incl_range F hj.le] at H; obtain ⟨q,rfl⟩:= H
 let k : Who G 6→ Labels.Key G:=Subtype.val
 let C:=cloak F (incl F hj.le q)
 let D:=Finsupp.single c 1+ Finsupp.single b 1+ Finsupp.single a 1
 by_contra h
 have hh : D∈C.support := by
   have hp : 0∈(D1 c (D1 b (D1 a C))).support := mem_support_iff.mpr h
   simpa only [D,zero_add] using leafup _ _ (leafup _ b (leafup _ c hp))
 let Q:=RawLabels.physicalLabel F j q
 have he : uncap C=Q.val := by
   unfold C; rw [stretch,Full.sections,LinearMap.comp_apply,RawLabels.physical_inclusion F (Free.scheme_filters F) hj.le];rfl
 have hD : Finsupp.mapDomain k D∈Q.val.support:=by rw [←he,mem_support_iff,uncap,coeff_rename_mapDomain k Subtype.val_injective]; exact mem_support_iff.mp hh
 have hz : Labels.height (Finsupp.mapDomain k D) ≤ j:= (mem_restrictSupport_iff ℂ).1 (show Q.val∈Labels.limited G j from Q.property.1) hD
 simp only [Labels.height,D,Finsupp.mapDomain_add,Finsupp.mapDomain_single,map_add,Finsupp.weight_single, one_smul,Labels.generation,k] at hz; omega
lemma root_map_bar {I : Type*} (p : Cache I) (a b c:I) : root3 (MvPolynomial.map (starRingEnd ℂ) p) a b c = star (root3 p a b c) := by simp only [root3,D1, pderiv_map,coeff_map];rfl
lemma moon_shift (T : Sky G (Per n)) (K : Who G d → FullT G n) (p:E F d) (o : Site n) (h:ℝ) : star (moon K h o T (cloak F p))=moon K h o T (cloak F (bar F d p)) := by
 change _=moon _ _ _ _ (cloak F ((freeTable F).conj (table_spin F) d p)); simp [moon,barcloak,root_map_bar]
def currency (F : Labels.Frames G) (n : Side) (t : ℝ) : E F 6 →ₗ[ℂ] ℂ where
 toFun p := moon (torT n 6 t 0) t 0 (lapSky G n) (cloak F p)
 map_add' p q:=by simp only [moon,root3,D1, ←robes_eq,map_add, coeff_add, add_mul, Finset.sum_add_distrib]
 map_smul' c p:=by simp only [moon,root3,D1,←robes_eq,map_smul, Derivation.map_smul, coeff_smul,RingHom.id_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
lemma saving (p:E F 6) (h:ℝ) (T : Sky G (Per n)) (K : Who G 6→FullT G n) (o : Site n) {j : ℕ} (hj:j<6) (hp : p∈lower F j 6): moon K h o T (cloak F p)=0:=by unfold moon; simp only [show ∀ a b c,_= _ from fun a b c=>tangI F a b c p j hj hp,zero_mul, Finset.sum_const_zero]
lemma spin_sky (A B C:FullT G n) (s:Signed) : lapSky G n (Bare.wideLink G s A) (Bare.wideLink G s B) (Bare.wideLink G s C)=lapSky G n A B C := by
 unfold lapSky; simp only [LinearMap.sum_apply,gear_push]; exact Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv (fun x=> ∑ i:Ticket,∑ j:Ticket,tower G x (icon (fresh i) (fresh j)) A B C)
lemma ride_bud (s : Signed): rideO F s.ortho d ((freeTable F).unit d)=(freeTable F).unit d := by apply writes_inj; erw [ride_at,writes_unit,map_one]
lemma billbar (n:Side)(t:ℝ)(p:E F 6): star (currency F n t p) = currency F n t ((freeTable F).conj (table_spin F) 6 p) := by
 rw [show currency F n t p=moon (torT n 6 t 0) t 0 (lapSky G n) (cloak F p) from rfl,moon_shift]; rfl
def sleeve (F : Labels.Frames G) (n : Side) (t : ℝ) : Buffer F 6 :=
 ⟨(((currency F n t).smulRight ((freeTable F).unit 6)).restrictScalars ℝ).toContinuousLinearMap, by
   have H (p : E F 6) : (((currency F n t).smulRight ((freeTable F).unit 6)).restrictScalars ℝ).toContinuousLinearMap p = currency F n t p • (freeTable F).unit 6:=rfl
   refine ⟨?_,?_,?_,?_,fun p=>?_⟩
   · rw [H]; rw [show currency F n t _ =0 from saving F _ t _ _ _ (j:=5) (by decide) (by rw [←incl_range F (by omega : (5:ℕ)≤6)]; exact ⟨_,incl_unit F _⟩),zero_smul]
   · intro e he p hp; rw [H, show currency F n t p=0 from saving F _ t _ _ _ he hp, zero_smul]; exact Submodule.zero_mem _
   · intro p; rw [H,H,map_smulₛₗ,Table.conj_unit]; have hv := billbar F n t p; rw [←hv];rfl
   · intro s p; rw [H,H,map_smul,ride_bud]; apply congrArg (· • _); symm
     let u:=swayL G 6 s; have ht := spin_pl G 6 s (X:=Per n) t; exact tint_moon _ t 0 _ _ _ _ u ht (fun x=> cirrus F s x p) (TintK _ u 0 t ht (turn_branch s)) (fun A B C=> spin_sky A B C s) -- check orientation
   exact ((currency F n t).smulRight _).map_smul _ p
 ⟩
lemma sleeve_eq (t : ℝ) (p:E F 6): (sleeve F n t).val p= currency F n t p • (freeTable F).unit 6:=rfl
end YM.RG11.FirstW
