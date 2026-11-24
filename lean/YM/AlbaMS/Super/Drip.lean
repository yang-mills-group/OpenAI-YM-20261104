import YM.AlbaMS.Super.Rune

/-!
# Coil transfer morphisms

For assigning variables linear homogeneous kernels in target. Finite supports
on consumed side assigned by given set (not necessarily including all old
kernel support; one can have projections annulling some generator with nowhere
to pass on a side). Commute Laplacians under transfer in pull-contraction
form. No invertibility assumption to prove this. Use e.g. when changing to
fixed ghost basis on even torus. Does not try to specify moving-source uses at
this abstraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function
open scoped BigOperators Classical
variable {ι κ R : Type*} [CommRing R] {ρ : ι→Bool} {σ : κ→Bool}
variable {F G : Coil ρ R} (k : ι→ι→R){s u : Finset ι}(t:Finset κ) {n :ℕ} {x :κ} {l : List κ}
variable (A : ι→κ→R)

def drip (s : Finset ι)(A : ι→ κ→R)(x:κ): Module.End R (Coil ρ R):=∑ i∈s, A i x • (D i)
lemma drip_apply : drip s A x F=∑ i∈s,A i x • (D i F):=by simp_rw [drip,LinearMap.sum_apply,LinearMap.smul_apply]

def drink (s : Finset ι)(A : ι→ κ→R) : List κ → Coil ρ R→ₗ[R] R
 | []=>{toFun:= fun x=> x [],map_add':=fun _ _=>rfl, map_smul':=fun _ _=>rfl}
 | x::l=> drink s A l ∘ₗ drip s A x
lemma drink_cons : drink s A (x::l) F=drink s A l (drip s A x F):=rfl
lemma drink_nil : drink s A [] F= F []:=rfl

lemma drained (h:Inside (s:Set ι) F)(H:s⊆u): drink s A l F=drink u A l F:=by
  induction l generalizing F with | nil=> rfl | cons x l ih=>
   rw [drink_cons,drink_cons,ih (by rw [drip_apply];exact Inside.sum _ _ fun i _=> ((h.dz i).smul _)), show drip s A x F=drip u A x F from ?_]; rw [drip_apply,drip_apply]; refine Finset.sum_subset H (fun i _ hi=>?_);rw [h.erased hi,smul_zero]

def Routes (ρ : ι→Bool)(σ : κ→Bool)(A : ι→ κ→R):Prop:=∀ i j,A i j≠0→ρ i= σ j
lemma drip_plane (H:Routes ρ σ A)(p : Bool): drip s A x (plane p F)=sting (p && σ x) (plane p (drip s A x F)):= by
  rw [drip_apply, drip_apply,map_sum,sting_sum]; refine Finset.sum_congr rfl fun i _=> ?_;by_cases hv:A i x=0; · simp [hv]
  rw [planeD,H i x hv,map_smul,sting_smul]
lemma drip_x (H:Routes ρ σ A)(x y : κ): drip s A y (drip s A x F)=sting (σ x && σ y) (drip s A x (drip s A y F)):=by
  rw [drip_apply A (s:=s) (x:=x),map_sum,drip_apply A (s:=s) (x:=y) (F:=F),map_sum,sting_sum]; simp_rw [map_smul,drip_apply,Finset.smul_sum,sting_sum]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; by_cases hu:A i y=0; simp [hu]; by_cases hz:A j x=0; simp [hz]; rw [DD F, H i y hu, H j x hz]; cases σ x<;>cases σ y<;>simp [smul_comm (A i y) (A j x)]
lemma flowing (H:Routes ρ σ A): Concord σ (fun l=> drink s A l F):=by
  intro a l i j; induction a generalizing F with | nil=>
    simp only [List.nil_append,drink_cons]; rw [drip_x A H]; cases σ i<;>cases σ j<;> simp
                                                  | cons x l ih=> exact ih

def shot {ρ : ι→Bool} {σ : κ→ Bool} (s : Finset ι)(A : ι→κ→R)(H:Routes ρ σ A): Coil ρ R→ₗ[R] Coil σ R where
  toFun F:=⟨fun l=> drink s A l F, flowing A H⟩
  map_add' _ _:= ext _ _ (fun l=> LinearMap.map_add (drink s A l) _ _)
  map_smul' c F:= ext _ _ (fun l=> map_smul (drink s A l) c F)
variable (H:Routes ρ σ A)
lemma shot_read : shot s A H F l=drink s A l F:=rfl
lemma shot_D : D x (shot s A H F)=shot s A H (drip s A x F):=rfl
lemma shot_nil : shot s A H F [] = F []:=rfl
include H in
lemma Tone.drips {p : Bool}(he : Tone p F): Tone (xor p (σ x)) (drip s A x F):= by
  rw [drip_apply]; refine Tone.sum _ _ (fun i hi=>?_); by_cases h:A i x=0; · simp [h,Tone.none]
  rw [← H _ _ h];exact (he.dz i).smul _
lemma shot_plane (p : Bool): shot s A H (plane p F)=plane p (shot s A H F):=by
  ext l; induction l generalizing F with
  | nil=> simp [shot_nil,polar]
  | cons x l ih=> rw [← D_read (F:=plane p _), ← D_read (F:=shot _ _ _ _), shot_D,planeD,drip_plane A H,shot_D]; cases h:p && σ x<;>simp [ih]
lemma shot_put (c:R): shot s A H (put ρ c)=put σ c:= by ext l; cases l; exact shot_nil ..; next x l=> rw [← D_read,shot_D,drip_apply]; simp
lemma shot_mul : shot s A H (F*G)=shot s A H F * shot s A H G:=by
  ext l; induction l generalizing F G with
  | nil=> simp [shot_nil]
  | cons i l ih=>
    have ht: drip s A i (F*G)=drip s A i F*G + plane (σ i) F *drip s A i G:=by
      simp_rw [drip_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,mul_smul_comm,mulD,smul_add]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=>?_ ; by_cases he:A j i=0; · simp [he]
      rw [H _ _ he]
    rw [mul_cons,← D_read (F:=shot _ _ _ (F*G)),shot_D,ht,map_add,plus_read,ih,ih,shot_D,shot_D,shot_plane]

def bar (s : Finset ι): Coil ρ R→ₐ[R] Coil σ R where
  __:= shot s A H
  map_zero':= (shot s A H).map_zero
  map_mul' _ _:= shot_mul A H
  map_one':=shot_put A H 1
  commutes' c:=shot_put A H c
lemma bar_eq : bar A H s F = shot s A H F := rfl
lemma shot_inside {t : Set κ} (ht:∀ i∈ s,∀ j ∉ t,A i j=0): Inside t (shot s A H F):=by
  intro l; induction l generalizing F with | nil=> simp | cons i l ih=>
    intro h j hj; rw [← D_read,shot_D] at h
    rcases List.mem_cons.1 hj with rfl|hv
    · by_contra hv; rw [show drip s A j F=0 from ?_,map_zero] at h; exact h rfl
      rw [drip_apply]; exact Finset.sum_eq_zero fun i hi=> by rw [ht i hi j hv,zero_smul]
    exact ih h _ hv
end YM.MSBar.Bric.Coil
