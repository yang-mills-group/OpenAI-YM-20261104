import YM.MS.Plane

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Finset Plane Koszul
variable {A R P:Type} [Fintype A] [CommRing R] [AddCommGroup P] {p: Koszul.Sector A} {b c:Bool}
structure Pilot (R P:Type)[CommRing R][AddCommGroup P](p:Koszul.Sector A) where
   volp : P≃+ P
   fieldC : A→ A→ R
   pair_zero (i j:A): fieldC i j≠0→ p i=p j
namespace Pilot
variable (K:Pilot R P p) (F:Row A P R)
def peer (K:Pilot R P p) (F: Row A P R) : Row A P R
| [] => F []
| i::l => ∑ a, K.fieldC i.1 a * peer K (D (a,K.volp i.2) F) l
termination_by l=> l.length
def beam (K: Pilot R P p): Op (Mode A P) R where
   toFun F:=peer K F
   map_add' i j:= funext fun l=>by induction l generalizing i j with| nil=> simp [peer]| cons a l ih=> simp only [peer,map_add,Pi.add_apply]; simp_rw [ih,Pi.add_apply,mul_add,Finset.sum_add_distrib]
   map_smul' c i:= funext fun l=>by induction l generalizing i with| nil=>simp [peer]| cons a l ih=> simp only [peer,map_smul]; simp_rw [ih,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_left_comm _ c,← Finset.mul_sum]; rw [peer]
@[simp] lemma peeps : beam K F []=F []:= peer.eq_1 ..
lemma met (i:Mode A P) l: beam K F (i::l)= ∑ a, K.fieldC i.1 a * beam K (D (a,K.volp i.2) F) l:= peer.eq_2 ..
lemma served (i:Mode A P): D i (beam K F)= ∑ a,K.fieldC i.1 a • beam K (D (a,K.volp i.2) F):= by funext l; simp only [at_D,met,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
lemma offset (v w: Row A P R)(u:P)(l:Legs (Mode A P))(he:∀ i,net i=K.volp u → v i=w i)(hl:net l=u): beam K v l=beam K w l:= by
    induction l generalizing v w u with
    | nil=> simp only [peeps]; exact he [] (by rw [← hl]; simp [net])
    | cons i l ih=> rw [met,met]; refine Finset.sum_congr rfl fun a _=> ?_; rw [ih (v:=D (a,K.volp i.2) v) (u:=net l) (w:=D (a,K.volp i.2) w) (fun f hp=> show v ((a,_)::f)=w ((a,_)::f) from he ((a,K.volp i.2)::f) (by rw [net_cons, hp,← map_add,← net_cons (x:=i),hl])) rfl]
lemma beam_sign (b:Bool): beam K (sign (field p) b F)=sign (field p) b (beam K F):= by
   funext l; induction l generalizing F with
   | nil=> simp
   | cons i l ih=> simp only [D_eval i]; rw [ K.served, sign_D, K.served]; simp_rw [map_sum, map_smul, Finset.smul_sum, sign_D, map_smul, Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ih]; refine Finset.sum_congr rfl fun a _=>?_ ; by_cases h:K.fieldC i.1 a=0; simp [h]; change K.fieldC i.1 a * (cross b (p a) * _) =_ -- order of cross? inspect
                   dsimp only [field]; rw [K.pair_zero _ a h]; ring
lemma circle_prod (x: Row A P R) : beam K (product (field p) F x)=product (field p) (beam K F) (beam K x):= by
   funext l; induction l generalizing F x with
   | nil=>simp
   | cons i l ih=> -- D_prod
       simp only [D_eval i]; rw [ served,D_product,served,served]; simp only [D_product,map_add,Finset.sum_add_distrib, map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,Pi.add_apply, ih,smul_add,Finset.sum_add_distrib]; congr 1; refine Finset.sum_congr rfl (fun a _=> ?_); by_cases hw:K.fieldC i.1 a=0; simp [hw]; simp_rw [field, K.pair_zero _ a hw,beam_sign] -- only terms
end Pilot
end YM.MS.Arts
