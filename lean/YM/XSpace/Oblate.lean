import YM.XSpace.Organ
/-!
# Collected bulk (actually the full b, witness-dependent)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Graph3 Gland Chart2 Octave Season Lattice Chiral MvPolynomial Player Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(x y z w:Cover)
local notation "L" => Name G
local notation "M" => mum W
local notation "Y" => mrs W
local notation "F" => playAll W g x y z
abbrev Φx (p:PlaqAxes)(w:Cover)(i j k:L):= feet x y z ((M i).origin g) ((Y j).origin g) ((Y k).origin g) (V3 G (tile p)) w
lemma φX (p:PlaqAxes)(w:Cover): mainQ W g x y z (w,p)= F (Φx W g x y z p w):= by unfold mainQ; rw [encoded]; rfl
lemma latch_at (i j k:L): weightX W g x y z i j k=∑ p:PlaqAxes,∑' w:Cover,Φx W g x y z p w i j k:=courtesy (M i) (Y j) (Y k) g x y z _ _ (fun p _=> k₃ (primary _))
lemma φT (p:PlaqAxes)(i j k:L): Summable (fun w:Cover=> Φx W g x y z p w i j k):= entry ((M i).visit g) ((Y j).visit g) ((Y k).visit g) (primary p) x y z
lemma play_sum (p:Cover→ L→L→L→ℂ)(h:∀ i j k,Summable fun w=> p w i j k): Summable (fun w:Cover=> F (p w)) ∧ (∑' w:Cover,F (p w))= F (fun i j k=>∑' w:Cover,p w i j k):=by
  let b:=bstep W g x; let a:=u_line g W y; let c:= u_line g W z; let fee i j k l m:ℂ:=6*fuel k l m*b l (a i)*b m (c j); let P i j k l m (w: Cover):=fee i j k l m*p w k i j
  have he : ∀ i j k l m:L,HasSum (P i j k l m) (fee i j k l m*∑' w,p w k i j) := fun _ _ _ _ _=> ((h ..).hasSum.mul_left _) -- .. issue
  have ht:= hasSum_sum (fun i (_:i∈Finset.univ)=> hasSum_sum (fun j (_:j∈Finset.univ)=> hasSum_sum (fun k (_:k∈Finset.univ)=> hasSum_sum (fun l (_:l∈Finset.univ)=> hasSum_sum (fun m (_:m∈Finset.univ)=> he i j k l m))))) -- syntax
  exact ⟨ht.summable,ht.tsum_eq⟩
lemma profits (p:PlaqAxes) : Summable (fun w:Cover=> mainQ W g x y z (w,p)) := by simp_rw [φX]; exact (play_sum W g x y z (Φx W g x y z p) (φT W g x y z p)).1
lemma paying_play : F (weightX W g x y z)= ∑ p:PlaqAxes,∑' w:Cover, mainQ W g x y z (w,p):=by
  simp_rw [φX, (play_sum W g x y z (Φx W g x y z _) (φT W g x y z _)).2]; let p (i:PlaqAxes)(j k l:L):= ∑' w:Cover,Φx W g x y z i w j k l; change _=∑ t:PlaqAxes, F (p t); rw [show weightX W g x y z=fun i j k=>∑ t,p t i j k from funext fun i=> funext fun j=> funext fun k=> latch_at ..]
  unfold playAll scoreX; simp_rw [Finset.mul_sum,Finset.sum_comm (s:=(Finset.univ:Finset L)) (t:=(Finset.univ:Finset PlaqAxes))]
abbrev Seal := upper W g y z (b_1 W x)+ mainPlay W g x y z - ∑ p:PlaqAxes,∑' w:Cover, mainQ W g x y z (w,p)
def trioW (i j k:L):ℂ:= rootBeam W g x y z i j k + (station W g x y z i j k+other W g x y z i j k)-weightX W g x y z i j k
lemma sealed : Seal W g x y z= F (trioW W g x y z):= by rw [Seal, ← paying_play, cap, mainPlay, played_flip W g x y z]; unfold playAll scoreX trioW other; simp only [mul_sub,mul_add,Finset.sum_add_distrib,Finset.sum_sub_distrib]
end YM.XSpace.Finale
