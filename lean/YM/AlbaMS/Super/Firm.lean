import YM.AlbaMS.Super.Plex

/-! Propagate interpretations of even coefficients to the formal ring of
Coil kernels, at fixed (but arbitrary) word size. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R S E : Type*} [CommRing R] [CommRing S] {ρ : ι→Bool} (p : Bool) (x : ι)
variable (F G H : Coil ρ R) (l : List ι) {n : ℕ} {k : ι→ι→R} {s : Finset ι}
namespace Coil
variable (J : R →+ S)
def seep (J : R→+ S) : Coil ρ R →+ Coil ρ S where
  toFun F:=⟨J∘F,fun a l i j=> by
    change J (F _)=sting _ (J (F _)); rw [show F (a++i::j::l)=_ from F.trusted a l i j]; cases ρ i<;>cases ρ j<;> simp ⟩
  map_zero':=ext _ _ (fun _=> J.map_zero)
  map_add' _ _:= ext _ _ (fun _=> J.map_add _ _)
lemma seep_read : seep J F l= J (F l):=rfl
lemma seep_plane : seep J (plane p F)= plane p (seep J F):=by ext l; simp only [polar,seep_read]; cases p<;>cases band ρ l<;>simp
lemma seep_D : seep J (D x F)= D x (seep J F):=rfl
lemma seep_put (c:R): seep (ρ:=ρ) J (put _ c)=put _ (J c):=by ext l; rw [seep_read]; cases l<;>simp
lemma Cap.seep (h:Cap F n): Cap (seep J F) n:=fun l hv=>h l fun he=>hv (by simp [seep_read,he])
lemma Heg.seep (h:Heg n F): Heg n (seep J F):=fun l hv=>h l fun he=>hv (by simp [seep_read,he])
lemma Inside.seep {s : Set ι}(h:Inside s F): Inside s (seep J F):= fun l hv => h l (fun he=>hv (by simp [seep_read,he]))
lemma Tone.seep (h:Tone p F): Tone p (seep J F):=fun l hv=>h l fun he=>hv (by simp [seep_read,he])
lemma seep_derive (Z : R→+ R)(t : ∀ x y, Z (x*y)=Z x*y+x* Z y): seep Z (F*G) = seep Z F* G+ F* seep Z G:=by
  ext l; induction l generalizing F G with
  | nil=> simpa only [plus_read,tap_mul,seep_read] using t (F []) (G [])
  | cons x l ih=> rw [← D_read (F:=seep Z _) , ← seep_D, mulD,map_add]; simp only [plus_read, mul_cons, ← seep_plane,← seep_D,ih]; abel -- adjust arg
-- when scalars multiply simply across this interpretation
lemma seep_smul (c:R)(b:S)(h:∀ x, J (c*x)=b*J x): seep J (c • F)= b • seep J F:= ext _ _ fun l=> h (F l)
lemma seep_touch {L : ι→ι→S}(h:∀ i j x, J (k i j*x)=L i j*J x): seep J (touch k s F)=touch L s (seep J F):=by simp_rw [touch_apply, map_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [seep_smul _ _ _ _ (h i j),seep_D, seep_D]

-- convolution for projected coefficient ring on products
lemma seep_many (v:Finset E) (A B:E→ R→+S)(h:∀ x y,J (x*y)=∑ i∈v,A i x* B i y): seep J (F*G)=∑ i∈v,seep (A i) F* seep (B i) G:=by
  ext l; induction l generalizing F G with
  | nil=> simp only [sum_read,tap_mul,seep_read,h]
  | cons x l ih=>
    nth_rw 1 [← D_read _ _ x]; rw [← seep_D,mulD, map_add,plus_read,ih,ih];
    simp only [sum_read,mul_cons,← seep_D,← seep_plane, Finset.sum_add_distrib]
lemma seep_many_cross (v:Finset E)(A B:E→ R→+ S)(h:∀ x y,J (x*y)=∑ i∈v,A i x * B i y) {L : ι→ι→S} (hr:Graded ρ p k) (hp:Graded ρ p L) (hb:∀ i j x,J (k i j*x)=L i j*J x):
    seep J (cross p k s F G)=∑ i∈v,cross p L s (seep (A i) F) (seep (B i) G):= by
  have hc (i j : ι) : seep J (link ρ i j F G)=∑ u∈v,link ρ i j (seep (A u) F) (seep (B u) G):=by unfold link; rw [map_add, seep_many _ _ J v A B h,seep_many _ _ J v A B h]; simp_rw [seep_plane,seep_D,seep_plane]; rw [Finset.sum_add_distrib]
  simp_rw [from_cross p _ _ _ _ hr,from_cross p _ _ _ _ hp,map_sum]; -- smul and commute
  rw [Finset.sum_comm (s:=v)]
  refine Finset.sum_congr rfl fun i _=> ?_; rw [Finset.sum_comm (s:=v)]; refine Finset.sum_congr rfl fun j _=> ?_
  rw [seep_smul _ _ _ _ (hb i j),hc,Finset.smul_sum]

variable (P : R→+* S)
def Wind (ρ : ι→Bool)(P:R→+* S): Coil ρ R→+* Coil ρ S where
  __:=seep P.toAddMonoidHom
  map_one':= (seep_put P.toAddMonoidHom 1).trans (by change put _ (P 1)=_; rw [P.map_one];rfl)
  map_mul' F G:= by
    change seep P.toAddMonoidHom _=_
    have h:=seep_many F G P.toAddMonoidHom ({()}:Finset Unit) (fun _=> P.toAddMonoidHom) (fun _=> P.toAddMonoidHom) (fun x y=> by simp)
    rw [Finset.sum_singleton] at h;exact h
lemma blows : Wind ρ P F= seep P.toAddMonoidHom F:=rfl
lemma Wind_smul (c:R): Wind ρ P (c • F)=P c • Wind ρ P F:=ext _ _ (fun l=>P.map_mul _ (F l))
lemma Wind_cross : Wind ρ P (cross p k s F G) = cross p (fun i j=> P (k i j)) s (Wind ρ P F) (Wind ρ P G):=by
  unfold cross; have h F : Wind ρ P (touch k s F)= touch (fun i j=> P (k i j)) s (Wind _ P F):= seep_touch F P.toAddMonoidHom (fun _ _ x=> P.map_mul _ x)
  rw [map_sub,map_sub,map_mul (Wind _ P),map_mul (Wind _ P),h,h,h,map_mul]; rw [show Wind _ _ (plane _ _) = plane p (Wind ρ P F) from seep_plane p F _]
end Coil
end YM.MSBar.Bric
