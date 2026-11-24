import YM.MS.KoszulSyms
import YM.MS.Motif.Binary

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset Metric Real
open Plane Koszul Heat Flux
open scoped Topology
variable {A P R:Type} [CommRing R] [AddCommGroup P] {p:Sector A} {u f:Row A P R} {i:A}
local infixl:67 "⋄"=> product (field p)
def moment (s:P→+R) : Op (Mode A P) R where
    toFun f w:= s (net w)*f w
    map_add' _ _:= funext fun _=> mul_add ..
    map_smul' _ _:= funext fun _=> mul_left_comm ..
lemma moon (s:P→+R)(f:Row A P R)(l:Legs (Mode A P)): moment s f l=s (net l)*f l:= rfl
lemma blends (s:P→+R)(F H:Row A P R) : moment s ( F⋄H )= moment s F ⋄ H + F ⋄ moment s H:= by
   funext l; rw [moon,scattered,Pi.add_apply]; simp_rw [scattered]; let Z:= allocate (field p) l (R:=R); change s _ • Z _ = Z _+ Z _; rw [← map_smul, ← map_add]; apply scatter_congr; intro x y h; simp only [Pi.smul_apply,Pi.add_apply,moon,← split_net h,map_add,smul_eq_mul]; ring
lemma rail (s t:P→+R): moment s (moment t f)=moment t (moment s f):= funext fun _=>mul_left_comm ..
lemma moment_D (s:P→+R)(i:Mode A P): D i (moment s f)= s i.2 • D i f+ moment s (D i f):=by ext; simp only [Pi.smul_apply,at_D,moon,net_cons,map_add,add_mul,Pi.add_apply,smul_eq_mul]
lemma momentum_op (s:P→+R): moment s ( quash p i u f)=quash p i u (moment s f):= by
    funext l; simp_rw [moon,quamped,tip]; let Z:= allocate (field p) l (R:=R); change s _ • Z _= Z _; rw [← map_smul]; apply scatter_congr; intro x y h; simp only [Pi.smul_apply,moon,net_cons,split_net h,smul_eq_mul]; ring
lemma coin_v {r:R}: quash p i u (coin r)=0:= by
    funext l; unfold quash tip; simp only [LinearMap.mk₂_apply,coin,mul_zero]; exact map_zero (allocate ..) -- cost
variable [DecidableEq A]
def note (i:A)(d:P→R) : Row A P R:= mono (fun x:Mode A P=> if x.1=i then d x.2 else 0)
omit [AddCommGroup P] in lemma node1 (a:A)(f:P→R)(i:Mode A P): note a f [i]= if i.1=a then f i.2 else 0:= rfl
omit [AddCommGroup P] in lemma nodeD (a:A)(f:P→R)(i:Mode A P): D i (note a f)= coin (if i.1=a then f i.2 else 0):= by ext v; cases v <;> rfl
omit [AddCommGroup P] in lemma note_p (a:A)(f:P→R): Pure (field p) (p a) (note a f):= by rintro (_|⟨i,_|k⟩) h <;> first| rfl | (exact if_neg (fun he=> h (by simp [field,he]))) -- bug both
omit [AddCommGroup P] in lemma note_sym (a:A)(d:P→R): Symm (field p) (note a d):= by intro l; rcases l with _|⟨a,_|s⟩ <;> simp [note,mono]
lemma note_q (a i:A)(f:P→R) (w:Legs (Mode A P)): quash p i u (note a f) w= if a=i then u w*f (net w) else 0:= by
   rw [quamped,tip]; change scatter _ w (fun l r=> u l* D (i,net l) (note a f) r)=_; simp_rw [nodeD];
   classical
   have H (G : Row A P R)(w : Legs (Mode A P)) : scatter (field p) w (fun l r=> if r.length=0 then G l else 0)=G w:= by
       induction w generalizing G with| nil=> rfl| cons a w ih=> rw [scatter_cons]; simp only [List.length_cons,Nat.succ_ne_zero,↓reduceIte,mul_zero,add_zero]; exact ih (fun l=>G (a::l))
   have he (l r:Legs (Mode A P))(i:R) : u l*coin i r= if r.length=0 then u l*i else 0:= by cases r <;> simp [coin]
   by_cases h:a=i; simp_rw [if_pos h.symm,he,H]; rw [if_pos h];
   simp_rw [if_neg (Ne.symm h), he,mul_zero]; simp only [ite_self, if_neg h]; exact map_zero (allocate ..)
end YM.MS.Motif
