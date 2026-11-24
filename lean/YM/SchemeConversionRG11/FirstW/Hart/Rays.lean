import YM.SchemeConversionRG11.FirstW.Hart.Listen
/-! Speed coordinates on native flags. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Topology Maxwell Submodule
open scoped BigOperators Classical InnerProductSpace
variable {T : Itinerary} {G : Gauge} {k : ℕ} {r : ℝ}
def tipAt (a : Axis) (k : List Axis) (v : G.ColorIndex) : Field4 G→ₗ[ℝ] ℝ where
 toFun p:= inner ℝ (unitColor G v) (combine k (field4 a p) 0)
 map_add' u w:= by rw [show field4 a (u+w)=field4 a u+field4 a w from rfl,combine_add,Pi.add_apply,inner_add_right]
 map_smul' r w:= by rw [show field4 a (r • w)=r • field4 a w from rfl,combine_smul,Pi.smul_apply,real_inner_smul_right];rfl

def Mon (T : Itinerary) (k : ℕ) (W : ℕ→Field4 G) := ∀ i : ℕ,i≤k → ∀ (D : Fin i→Axis)(a : Axis)(v : G.ColorIndex), Helen (fun j=>(T.gap j^(i+1))⁻¹ * tipAt a (List.ofFn D) v (W j))
lemma tunedMon (W:ℕ→Field4 G) {Y : ℕ→Nu G k} (h: Court (fun i=> (T.gap i^(k+2))⁻¹ • (planR k (W i) - (Submodule.inclusion cabin_stor) (Y i)))) (hp : Mon T k W): Mon T k (fun i=>(Y i).val) := by
  intro i hi D a v; let E :=tipAt (G:=G) a (List.ofFn D) v
  let K := fun j => (T.gap j^(i+1))⁻¹ • (planR k (W j)- (Submodule.inclusion cabin_stor) (Y j))
  have hv : Level K := by
    have hv := T.cutoff.pow (k+1-i)
    have hw := Level.oil (h:=show Tendsto _ atTop (𝓝 0) from by simpa only [zero_pow (show k+1-i≠0 by omega)] using hv) h -- pow
    unfold K; convert! hw using 1; funext j; rw [smul_smul]; apply congrArg (· • _); rw [show k+2=k+1-i+(i+1) from by omega, pow_add _ (k+1-i),mul_inv]; field_simp [(T.positive j).ne']
  let P:= E.comp (stor G k).subtype; have he:= hv P; obtain ⟨c,hc⟩:=hp i hi D a v
  refine ⟨c,(sub_zero c) ▸ ?_⟩ -- brittle
  apply (hc.sub he).congr; intro j
  change _ - P (K j)=_; unfold K; rw [P.map_smul,P.map_sub];
  have hp' : P (planR k (W j))= E (W j) := by apply congrArg (inner ℝ (unitColor G v)) (scalp (List.ofFn D) (field4 a (W j)) (k+1) (by rw [List.length_ofFn]; omega))
  rw [hp']; change (T.gap j^(i+1))⁻¹ * E (W j)- (T.gap j^(i+1))⁻¹ *(E (W j)-E (Y j).val)=_; ring -- last not reducible
variable (T)
abbrev Age (G : Gauge) := (i:ℕ)→ ℕ→Nu G i
def composeR (k : ℕ) (a : Age G) (i : ℕ) := ∑ v∈Finset.range (k+1),T.gap i^(v+1) • (a v i).val
-- all gen coordinate choices suffice. outside set no growth used.
lemma luminosity (k : ℕ) (P : ℕ→ Nu G k) (h : Mon T k (fun i=> (P i).val)) : ∃ a : Age G,(∀ i≤k,Book (a i)) ∧ ∀ i,(P i).val = composeR T k a i := by
  induction k with
  | zero=>
    let A : ℕ → Nu G 0 := fun i=>(T.gap i)⁻¹ • P i
    let X := Fin.elim0 (α:=Axis)
    let c (x:Axis × G.ColorIndex):Low (Nu G 0):= tipAt x.fst (List.ofFn X) x.2 ∘ₗ (cabin G 0).subtype
    have hb : Book A := by
      intro L; refine offbook (a:=A) c ?_ (fun a=>?_)
      · intro u hu; rw [show u=0 from ?_,map_zero]; apply Subtype.ext; funext z; apply ink_zero; intro i
        have e := congrArg (inner ℝ (unitColor G i)) (loft_basis (cabin_floor u.property z.2) z.1)
        change inner ℝ (unitColor G i) _=0; apply e.trans
        have hh := hu (z.2,i); unfold c tipAt at hh; simpa only [LinearMap.comp_apply,LinearMap.coe_mk, AddHom.coe_mk,List.ofFn_zero,combine] using! hh
      obtain ⟨z,hz⟩:=h 0 le_rfl X a.1 a.2; refine ⟨z,hz.congr ?_⟩; intro j; unfold A; rw [(c a).map_smul]; exact (by simp only [zero_add,pow_one]; rfl)
    let m : Age G:= fun i=>match i with |0=>A|k+1=>0
    refine ⟨m,fun i hi=>?_,fun i=>?_⟩
    · rw [show i=0 from Nat.eq_zero_of_le_zero hi]; exact hb
    simp only [composeR, Finset.sum_range_succ, Finset.sum_range_zero,zero_add,pow_one,m,A]; erw [Submodule.coe_smul_of_tower]; rw [smul_inv_smul₀ (T.positive _).ne']
  | succ k ih=>
     let M:=cabin G k; let N:=cabin G (k+1); let S:M→ₗ[ℝ] N := Submodule.inclusion (stepped (Nat.le_succ k));
     obtain ⟨L,H⟩:=LinearMap.exists_leftInverse_of_injective S (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _))
     let D:= (LinearMap.id (R:=ℝ) (M:=↥N))-S.comp L
     let Q j := (T.gap j^(k+2))⁻¹ • D (P j)
     let Y:= (cabin G (k+1)).subtype
     let a (i : (Fin (k+1)→Axis) × Axis × G.ColorIndex):= tipAt i.2.1 (List.ofFn i.1) i.2.2 ∘ₗ Y
     have hc : Book Q := by
       intro B
       suffices H0:Helen (fun i=> B.comp D ((T.gap i^(k+2))⁻¹ • P i)) by unfold Q; simpa only [LinearMap.comp_apply,map_smul] using H0
       refine offbook (a:=fun i=> (T.gap i^(k+2))⁻¹ • P i) a ?_ ?_
       · intro u hu; have hu' : u.val∈stor G k := by
           refine stor_mem.mpr fun i L hl=>funext fun x=>?_
           have he : combine L (field4 i u.val)∈ Loft G.Color 0 := loft_scoped (k+1) 0 _ (show field4 i u.val∈Loft G.Color (0+(k+1)) from by rw [zero_add]; exact cabin_floor u.property i) _ hl -- field4 ..
           rw [loft_basis he]; apply ink_zero; intro v
           suffices e : ∃ q: Fin (k+1)→Axis,List.ofFn q=L by obtain ⟨q,hq⟩:=e; rw [←hq]; exact hu (q,i,v)
           have lists (j : ℕ) (hL : L.length=j) : ∃ q : Fin j→Axis,List.ofFn q=L := by subst j; exact ⟨L.get,List.ofFn_get L⟩
           exact lists _ hl
         have hq : u.val∈ M:= ⟨hu',cabin_lap u.property,cabin_div u.property⟩; let v :↥M:=⟨u.val,hq⟩; have e:S v=u:=Subtype.ext rfl; change B (D u)=0; rw [← e]; unfold D; rw [LinearMap.sub_apply,LinearMap.id_apply,LinearMap.comp_apply,show L (S v)=v from congrArg (fun f : M→ₗ[ℝ] M=> f v) H, sub_self,map_zero]
       intro i; obtain ⟨v,hv⟩:=h (k+1) le_rfl i.1 i.2.1 i.2.2; exact ⟨v,hv.congr (fun j=>by rw [(a _).map_smul]; rfl)⟩
     let V j :=L (P j)
     have he (i) : (P i).val=(V i).val + T.gap i^(k+2) • (Q i).val := by
       have h : P i= S (V i)+T.gap i^(k+2) • Q i := by
          unfold Q V D; rw [smul_inv_smul₀ (pow_ne_zero _ (T.positive i).ne'), LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.id_apply]; abel
       exact congrArg Subtype.val h
     have hp : Mon T k (fun i=>(V i).val) := by
        intro j hj Tn l v
        let X:=tipAt (G:=G) l (List.ofFn Tn) v
        obtain ⟨b,hb⟩:=h j (hj.trans (Nat.le_succ k)) Tn l v; obtain ⟨c,hc⟩ := hc (X.comp Y)
        have hp : Tendsto (fun i=> T.gap i^(k+1-j)) atTop (𝓝 0) := by simpa only [zero_pow (show k+1-j≠0 from by omega)] using T.cutoff.pow (k+1-j)
        refine ⟨_,(hb.sub (hp.mul hc)).congr (fun i=>?_ )⟩
        change (T.gap i^(j+1))⁻¹ * X (P i).val - (T.gap i^(k+1-j)* X (Q i).val)= (T.gap i^(j+1))⁻¹* X (V i).val
        rw [he,X.map_add,X.map_smul,smul_eq_mul, show T.gap i^(k+2)=_ from show T.gap i^(k+2)=T.gap i^(j+1)*T.gap i^(k+1-j) by rw [←pow_add,show j+1+(k+1-j)=k+2 from by omega]];field_simp [(T.positive i).ne']; ring
     obtain ⟨m,hm,hu⟩:=ih (fun i=>V i) hp
     let F:=Function.update m (k+1) Q
     refine ⟨F,fun j hj=>?_,fun i=>?_⟩
     · by_cases h:j=k+1;· subst j; rw [show F (k+1)=Q from update_self ..]; exact hc
       rw [show F j=m j from update_of_ne h ..]; exact hm j (by omega)
     rw [he,hu i,composeR,composeR,Finset.sum_range_succ (n:=k+1),show F (k+1)=Q from update_self ..] -- occurrences check
     refine congrArg₂ _ (Finset.sum_congr rfl (fun j hj=>?_)) rfl;rw [show F j=m j from update_of_ne (Finset.mem_range.mp hj |>.ne) ..]
end YM.RG11.FirstW
