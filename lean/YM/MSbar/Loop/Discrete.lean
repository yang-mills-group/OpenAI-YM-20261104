import YM.MSbar.Loop.Bond

/-! How the finite identities read on Fourier words, including outside grid and nonconserving
words. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Super Function Finset
open scoped Topology BigOperators Classical
variable {C M: Type*} [AddCommGroup M] {p:C→Bit} {I:Finset C}
variable {d:Bit} {f g : Amps C M} {S:Line C M} (L:Finset M)
def held (L:Finset M)(S:Line C M):Line C M:= fun a b t=> if t∈L then S a b t else 0

private def l (a b:C) (t:M) (p:C→Bit) (d:Bit) (S:Line C M)(f g:Amps C M) (x y:Field C M):=
    S a b t/2* sign (p b) (p a+d)*f ((a,t)::x)*g ((b,-t)::y)
private def r (a b:C) (t:M) (p:C→Bit) (d:Bit) (S:Line C M)(f g:Amps C M) (x y:Field C M):=
    S a b t/2* sign (p a) d*f ((b,-t)::x)*g ((a,t)::y)
private lemma at_slot (a b:C) (t:M) : (S a b t/2) • member (lift p) d ((a,t),(b,-t)) f g =
    split (lift p) (l a b t p d S f g + r a b t p d S f g):=by
    let L₁(x y):=f ((a,t)::x)*g ((b,-t)::y);let L₂(x y):= f ((b,-t)::x)*g ((a,t)::y)
    let x:=S a b t/2;let A:=sign (p b) (p a+d);let B:=sign (p a) d
    rw [split_add,member_pair]; change x•(A • split _ L₁+B • split _ L₂) = _
    have h:l a b t p d S f g=(x*A)•L₁:=funext fun u=>funext fun v=>mul_assoc ..
    have g:r a b t p d S f g=(x*B)•L₂:=funext fun u=>funext fun v=>mul_assoc ..
    rw [h,g,split_scale,split_scale,smul_add,smul_smul,smul_smul]
private lemma collapsed (hf:Quiet f) (a b:C)(x y:Field C M):
    (∑ t∈L,(l a b t p d S f g + r a b t p d S f g)) x y= price p d a b (held L S) f g x y:=by
    let k:=channel x; simp_rw [Finset.sum_apply,Pi.add_apply]; rw [Finset.sum_add_distrib]; apply congr_arg₂ (·+·)
    · have ht t (h:t≠-k) : l a b t p d S f g x y=0:= by unfold l; rw [hf _ (by simp only [channel_cons]; exact fun he=>h (eq_neg_of_add_eq_zero_left he)),mul_zero,zero_mul]
      by_cases hp : -k ∈ L
      · rw [Finset.sum_eq_single_of_mem (-k) hp (fun t _ h=> ht t h)]; unfold held l; change _=(if -k∈L then _ else _)/_*_; rw [if_pos hp]; dsimp only [k]; simp only [neg_neg]; ring
      rw [Finset.sum_eq_zero (fun t h=> ht t (fun he=> hp (he ▸ h)))]; unfold held; simp [show -channel x∉ L from hp]
    have ht t (h:t≠k) : r a b t p d S f g x y=0:= by unfold r; rw [hf _ (by simp only [channel_cons]; exact fun he=> h ((neg_add_eq_zero.mp he))),mul_zero,zero_mul]
    by_cases hp : k∈L
    · rw [Finset.sum_eq_single_of_mem k hp (fun t _ h=> ht t h)]; unfold held r; change _=(if k∈L then _ else _)/_*_; rw [if_pos hp]; dsimp only [k]; ring
    rw [Finset.sum_eq_zero (fun t h=>ht t (fun he=>hp (he ▸ h)))]; unfold held; simp [show channel x∉L from hp]
lemma moment_pair (hf:Quiet f) : pairs (lift p) d (Stocking I L S) f g= tree p I d (held L S) f g:=by
    unfold Stocking; simp_rw [pairs_sum]; simp only [LinearMap.sum_apply,pairs_single,at_slot]; rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (s:=L) (t:=I)]
    funext v; unfold tree; simp only [Finset.sum_apply]; refine Finset.sum_congr rfl fun a ha=> Finset.sum_congr rfl fun b hb=> ?_
    rw [← Finset.sum_apply v L,← split_sum]; apply split_change; intro y w ht; exact collapsed L hf a b y w
lemma pair_quiet (hf: Quiet f)(hg:Quiet g): Quiet (pairs (lift p) d (Stocking I L S) f g):= (moment_pair L hf) ▸ hg.tree
end YM.MSbar.Loops
