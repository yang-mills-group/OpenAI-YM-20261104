import YM.AlbaMS.Loft.Loft

/-! Certify unscaled vertex data. No Legendre transform here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Loft
open Set Function Finset Bric Coil
open scoped BigOperators Classical
variable {E B R : Type*} [CommRing R] [Fintype E] [Fintype B]
def expandFloor (f : E→Floor E B R)(u : B→Floor E B R) : Module.End R (Floor E B R):=
    (∑ i:E,(LinearMap.mulLeft R (f i)).comp (DA i)) + ∑ i:B,(LinearMap.mulLeft R (u i)).comp (DC i)
variable (f : E→Floor E B R)(u : B→Floor E B R){F G S : Floor E B R}
lemma expands (F : Floor E B R): expandFloor f u F=(∑ i:E,f i* DA i F)+∑ i:B,u i* DC i F:=by simp only [expandFloor, LinearMap.add_apply, LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply]
lemma likes (hf:∀ i,OddT (f i))(ht: ∀ i, EvenT (u i)) (F G : Floor E B R): expandFloor f u (F*G)=expandFloor f u F *G+plane true F *expandFloor f u G:=by
  have hu (i:E): f i * DA i (F*G)= f i* DA i F *G+plane true F*(f i * DA i G):=by rw [show DA i (F*G)=DA i F*G+ F* DA i G from rfl,mul_add,← mul_assoc (f i) F,(hf i).slider F,mul_assoc,mul_assoc]
  have hv (i:B): u i * DC i (F*G)= u i* DC i F *G+plane true F*(u i * DC i G):=by rw [show DC i (F*G)=DC i F*G+ plane true F* DC i G from rfl,mul_add,← mul_assoc (u i) (plane true F), (ht i).slider (plane true F),polar_false,mul_assoc,mul_assoc]
  simp_rw [expands,hu,hv,Finset.sum_add_distrib,add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]; abel
lemma symbol_A (i:E):expandFloor f u (A R i)= f i:=by simp [expands,A, DA,DC, Place.a,Place.c,mul_ite]
lemma symbol_C (i:B):expandFloor f u (C R i)= u i:=by simp [expands,C, DA,DC, Place.a,Place.c,mul_ite]
@[simp] lemma symbol_K (i:E):expandFloor f u (K R i)=0:=by simp [expands,K, DA,DC, Place.a,Place.c,Place.k]
@[simp] lemma symbol_L (i:B):expandFloor f u (L R i)=0:=by simp [expands,L, DA,DC, Place.a,Place.c,Place.l]

def feeds (F:Floor E B R):= F+(∑ i:E,K R i*f i)-∑ j:B,L R j*u j
structure ConsoleF (f : E→Floor E B R)(u:B→Floor E B R) : Prop where
  jazz i : OddT (f i)
  hue j : EvenT (u j)
  lean i : Under (f i)
  strip j : Under (u j)
namespace ConsoleF
variable {f u} (hf:ConsoleF f u)
include hf
lemma emits (h:EvenT F): EvenT (feeds f u F) :=(h.add (Tone.sum _ _ fun i _=> (var_tone (R:=R) (ρ:=ø) (Place.k i)).mul (hf.jazz i))).sub (Tone.sum _ _ fun i _=> (var_tone (R:=R) (ρ:=ø) (Place.l i)).mul (hf.hue i))
lemma dk_point (h:Under F)(i:E): DK i (feeds f u F)=f i:=by
  simp only [feeds,map_sub,map_add,map_sum,h.1 i];
  have hg (j) : D (Sum.inl (Sum.inr i)) (f j)=0:=(hf.lean j).1 i; have he (j):D (Sum.inl (Sum.inr i)) (u j)=0:=(hf.strip j).1 i; simp [DK,K,L,mulD, Place.k, Place.l,ite_mul,hg,he]
lemma dl_point (h:Under F)(j:B): DL j (feeds f u F)= -(u j):=by
  have hg (i) : D (Sum.inr (Sum.inr j)) (f i)=0:=(hf.lean i).2 j; have he (i):D (Sum.inr (Sum.inr j)) (u i)=0:=(hf.strip i).2 j; simp [DL,feeds,map_sum,K,L,mulD,Place.k,Place.l,ite_mul, he,hg,(show D (Sum.inr (Sum.inr j)) F=0 from h.2 j)]
lemma height (h:Under F): delta (feeds f u F) = (∑ i:E, DA i (f i))+∑ i:B, DC i (u i):= by
  simp_rw [dots, hf.dk_point h,hf.dl_point h]; simp [Finset.sum_neg_distrib] -- g unused
lemma surf (h:EvenT F)(hp:Under F)(hh:Under G): coupling (feeds f u F) G = expandFloor f u G:=by
  rw [connects _ _ (hf.emits h),expands]; simp_rw [hf.dk_point hp,hf.dl_point hp, hh.1 _,hh.2 _,mul_zero]; simp [Finset.sum_neg_distrib]
variable [Algebra ℚ R]
omit hf in
def CMaster (k : Place E B → Place E B → R)(F : Floor E B R):= halve R • cross true k Finset.univ F F
theorem top (h:EvenT F)(H:Under F)(a:expandFloor f u F=0)(b:∀ i,expandFloor f u (f i)=0)(c:∀ j,expandFloor f u (u j)=0): CMaster (oriented R) (feeds f u F)=0:=by
  let S:= feeds f u F
  have he : expandFloor f u S=0:=by
    simp_rw [S,feeds,map_sub,map_add,map_sum,likes f u hf.jazz hf.hue]; simp [a,b,c]
  have hh:coupling S S = expandFloor f u S+expandFloor f u S:=by
    rw [connects _ _ (hf.emits h)]; have hg : EvenT S:= hf.emits h
    have ht (i:E): DA i S* DK i S=f i * DA i S:=by rw [hf.dk_point H]; exact (show EvenT (DA i S) from hg.dz (Place.a i)).slider (f i)
    have hl (j:B): DC j S*DL j S= -(u j)*DC j S:=by rw [hf.dl_point H j]; exact ((hf.hue j).neg.slider (DC j S)).symm
    dsimp only [S] at ht hl; simp_rw [S,ht,hl,hf.dk_point H,hf.dl_point H,expands, neg_mul,Finset.sum_neg_distrib]; abel
  rw [CMaster,show cross true _ Finset.univ _ _=coupling S S from rfl,hh,he,add_zero,smul_zero]
end ConsoleF
end YM.MSBar.Loft
