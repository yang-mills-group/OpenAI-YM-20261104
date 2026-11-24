import YM.MSbar.Origin.Charm

/-!
# CE and representation, lift of a Lie derivative
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin
open Function Set Filter Topology Super Finset
open scoped BigOperators ContDiff
variable {α β M J : Type*} {p : β → Bool}
namespace Canon
variable (K : Canon α β p) (T : α → Term β) [Fintype α]

lemma guide_smul (f : Term β) (c : ℂ) : K.guide T (c • f)=c • K.guide T f := by simp only [guide,peel_smul,mix_smul_last,smul_sum]
lemma guide_sum (f : M→Term β) (s : Finset M) : K.guide T (∑ i∈s,f i)=∑ i∈s,K.guide T (f i) := by simp only [guide,peel_sum,mix_sum_last]; exact sum_comm
lemma guide_letter [DecidableEq β] (a : α) : K.guide T (letter (K.leaf a))=T a := by
  classical
  unfold guide; rw [sum_eq_single a] <;> simp +contextual [peel_letter]
lemma guide_mix (K : Canon α β p) {T : α→Term β} (F : ∀ a,Grade p (p (K.anti a)) (T a)) {r : Bool} {f : Term β} (G : Grade p r f) (g : Term β) : K.guide T (mix p f g)=
    mix p (K.guide T f) g+twist true r • mix p f (K.guide T g) := by
  simp only [guide,G.peel_mix,mix_add_last,mix_smul_last,mix_sum_first,mix_sum_last,smul_sum,sum_add_distrib]; congr 1
  · apply sum_congr rfl; intro a _; rw [grade_mix_assoc (F a) (G.peel (K.leaf a))]
  apply sum_congr rfl; intro a _; rw [← grade_mix_assoc (F a) G, grade_mix_comm (F a) G,mix_smul_first,grade_mix_assoc G (F a),smul_smul,K.flips,twist_xor,←mul_assoc,twist_mm,one_mul]
end Canon
namespace Charm
variable (K : Charm M J β p) [Fintype M] [DecidableEq M]
def route (V : House M→House M) (f : House M→ℝ) (x : House M) := stunt f (V x) x
omit [DecidableEq M] in
lemma route_eager {V : House M→House M} {f : House M→ℝ} {x} (H : Eager V x) (F : Eager f x) : Eager (route V f) x := (F.fderiv_right (m:=ω) (by simp)).clm_apply H

lemma lamp (x : House M) : x=∑ i,x i • onePiece i := by ext v; simp [onePiece, Pi.single_apply]
lemma route_along (V : House M → House M) (f : House M→ℝ) : route V f=∑ i, pick V i * stunt f (onePiece i) := by
  funext x; unfold route; rw [lamp (V x)]; simp [stunt,pick]
variable [Fintype J] [DecidableEq β] {V : Canal M J} {D : Beamish J} {f : House M→ ℝ}
lemma operate_send (h : ∀ j,Eager (V j) 0) (H : Eager f 0) : K.operate V D (K.send f)=∑ j, mix p (K.ghost j) (K.send (route (V j) f)) := by
   unfold operate Canon.guide; rw [Fintype.sum_sum_type];
   change (∑ i,mix _ (K.poses _ i) (peel (K.prime i) (K.send f)))+(∑ j,mix _ (K.trunk _ j) (peel (K.shade j) (K.send f)))=_
   simp only [shade_send, mix_last_zero,sum_const_zero, add_zero,poses,mix_sum_first,K.peel_send]; rw [sum_comm]; apply sum_congr rfl; intro i _
   rw [route_along,send,bose_sum K.view (f:=fun j => pick (V i) j*stunt f (onePiece j)) (fun j _ => by exact (pick_eager (h i) j).mul (stunt_eager H (onePiece j))),mix_sum_last];
   refine sum_congr rfl fun j _ => ?_; rw [grade_mix_assoc (K.grade_ghost i) (K.grade_send _), bose_prod _ (pick_eager (h i) j) (stunt_eager H _) K.view_odd]


/-- Representation equation at germ level. The direction indices have no rank
projection. Uses [Qi,Qj] in action on coordinate functions. -/
def TurnsAlong (V : Canal M J) (D : Beamish J) := ∀ i j m, route (V i) (pick (V j) m)-route (V j) (pick (V i) m)=ᶠ[𝓝 0] ∑ k,D k i j • pick (V k) m

omit [Fintype M] [DecidableEq M] in
private lemma contributes (F : J → J → Term β) :
    (∑ i:J,∑ j,mix p (K.duplex i j) (F i j)) = (1/2:ℂ) • ∑ i:J,∑ j,mix p (K.duplex i j) (F i j-F j i) := by
   simp only [mix_sub_last,sum_sub_distrib]; conv_rhs => rhs; rhs; rw [sum_comm]
   have he : (∑ j:J,∑ i:J,mix p (K.duplex i j) (F j i))= -(∑ i:J,∑ j,mix p (K.duplex i j) (F i j)) := by
      simp only [←sum_neg_distrib]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rw [K.duplex_swap b a,mix_neg_first]
   rw [he]; module
omit [Fintype M] [DecidableEq M] [Fintype J] in
private lemma driveAlong (i j : J) (f : Term β) : mix p (K.ghost i) (mix p (K.ghost j) f)=mix p (K.duplex i j) f := (grade_mix_assoc (K.grade_ghost i) (K.grade_ghost j) f).symm
private lemma chime (h : ∀ j,Eager (V j) 0) (j : J) (F : Eager f 0) : K.operate V D (mix p (K.ghost j) (K.send f))=mix p (K.trunk D j) (K.send f) +∑ i, mix p (K.duplex i j) (K.send (route (V i) f)) := by
   change K.toCanon.guide _ _=_; rw [K.toCanon.guide_mix (K.grade_lift _ _) (K.grade_ghost j), show K.toCanon.guide (K.lift V D) (K.ghost j)=_ from K.toCanon.guide_letter _ (.inr j),← show K.operate V D=K.toCanon.guide (K.lift V D) from rfl, K.operate_send h F,mix_sum_last,twist_true,neg_smul,one_smul, ←sum_neg_distrib]
   congr! 1
   apply sum_congr rfl; intro i _; rw [K.driveAlong,K.duplex_swap j i,mix_neg_first,neg_neg]

lemma represents (h : ∀ j,Eager (V j) 0) (H : TurnsAlong V D) (a : M) : K.operate V D (K.poses V a)=0 := by
   unfold poses operate; rw [Canon.guide_sum]; change ∑ j:J,K.operate V D _=_;
   simp_rw [K.chime h _ (pick_eager (h _) a),sum_add_distrib]; apply add_eq_zero_iff_eq_neg.mpr
   conv_rhs => rhs; rw [sum_comm,K.contributes (fun i j => K.send (route (V i) (pick (V j) a)))]
   have ha i j : K.send (route (V i) (pick (V j) a))-K.send (route (V j) (pick (V i) a)) = ∑ k,(D k i j:ℂ) • K.send (pick (V k) a) := by
     unfold send; rw [←bose_sub _ (route_eager (h i) (pick_eager (h j) _)) (route_eager (h j) (pick_eager (h i) _)),bose_congr _ (H i j a)];
     simp_rw [bose_sum K.view (f:=fun k => D k i j • pick (V k) a) (fun k _ => (pick_eager (h k) a).const_smul (D k i j)), bose_smul K.view (pick_eager (h _) a)]
   simp_rw [ha]; simp only [trunk,mix_sum_last,mix_smul_first,mix_sum_first,mix_smul_last, neg_smul, ←sum_neg_distrib, smul_sum, mix_neg_first]
   rw [sum_comm]; apply sum_congr rfl; intro j _; exact sum_comm
end Charm
end YM.MSBar.Origin
