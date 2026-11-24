import YM.XSpace.Oblate
/-! # Score sum and the actual covariant root price -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Gland Angle Chart2 Octave Season Lattice Chiral MvPolynomial Player Graph3 Asymptotics Relief
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple){ι:Type} {C:Shade.Cut}{a:ι→ℝ}{F:Filter ι}{u v b:E4}{x y z:ι→Cover}
local notation "P₀"=> spoken
local notation "L"=>Name G
local notation "Υ"=>G.ColorIndex
local notation "M"=> mum W
local notation "Y"=> mrs W
local notation "λu"=> Player.quote -- syntax
local notation "T"=> atria
abbrev climax (c:Shade.Cut)(u v b:E4)(k i j:L):ℂ:=↑(br k.2 i.2 j.2* atria c k.1 i.1 j.1 u v b)
variable (p:Captain C F a x y z u v b)
private lemma locate_est (i j k:L) : kernel (Y j) (Y k) true u v b i=↑(br i.2 j.2 k.2*est i.1 j.1 k.1 u v b):=by unfold kernel; apply congr_arg; congr 1; apply Finset.sum_congr rfl; intro h _; exact Finset.sum_congr rfl fun k hk=> (mul_assoc ..).symm
include p in
lemma tri_at (i j k:L)[F.IsCountablyGenerated][NeBot F]: Named F a 6 (fun w=> trioW W g (x w) (y w) (z w) i j k) (climax C u v b i j k):=by
  have he:= tone (M i) (Y j) (Y k) g p rfl rfl; have hp:= ((projects (Y j) (Y k) g p (M i)).add ((projects (M i) (Y k) g p.hop (Y j)).add (projects (M i) (Y j) g p.turn.turn (Y k)))).sub he; unfold trioW other; simp_rw [station_at]; -- definal
  let h:=kernel (M i) (Y k) false v u b j+kernel (M i) (Y j) false b u v k; let f(w) := trioW W g (x w) (y w) (z w) i j k; -- simp issue. adjust convert
  rw [real_seal] at hp; change Named F a 6 (fun t=> _ ) (kernel (Y j) (Y k) true u v b i + h-_) at hp; rw [← add_assoc,locate_est] at hp -- order
  simp only [add_sub_add_right_eq_sub] at hp
  unfold climax atria; rw [mul_sub,Complex.ofReal_sub]; exact hp
private abbrev emitted (r:E4)(i j:L):ℂ:= ↑(χ j.2 i.2* P₀ r i.1 j.1)
abbrev item (C:Shade.Cut)(u v b:E4)(i j k m n:L):ℂ:= (6*fuel i j k)* emitted (u-v) j m*emitted (u-b) k n * climax C u v b i m n
private lemma note₁ (j m n b k:L)(x y z:E4) (u v:Υ): item C x y z j m n (b.1,u) (k.1,v)=(6:ℂ)* fuel j m n* (↑(br j.2 u v * (χ u m.2 * χ v n.2)* P₀ (x-y) m.1 b.1 *P₀ (x-z) n.1 k.1 * T C j.1 b.1 k.1 x y z):ℂ):=by unfold item emitted climax; push_cast; ring
private lemma log (C:Shade.Cut)(i j k:L)(m n:P) : ∑ a:Υ,∑ b':Υ,item C u v b i j k (m,a) (n,b')=6*fuel i j k*(↑(br i.2 j.2 k.2 * (spoken (u-v) j.1 m * spoken (u-b) k.1 n * T C i.1 m n u v b)):ℂ):=by
  rw [Finset.sum_eq_single j.2]; rw [Finset.sum_eq_single k.2]; unfold item emitted climax; change (6*fuel i j k)* ↑(χ j.2 j.2 * _)* ↑(χ k.2 k.2* _) * _=_; simp only [χ_self,one_mul]; push_cast; ring
  · intro y hy he; unfold item emitted; rw [show χ ((n,y):Name G).2 k.2=0 from if_neg he.symm,zero_mul];simp
  · simp
  · intro y hy he; apply Finset.sum_eq_zero; intro a _; unfold item emitted; rw [show χ ((m,y):Name G).2 j.2=0 from if_neg he.symm,zero_mul]; simp
  simp
private lemma dross (i j k:L): (∑ m:L,∑ n:L,item C u v b i j k m n)=(Complex.ofReal (((6:ℝ)*br i.2 j.2 k.2^2)*(liftedSign i.1 j.1 k.1 * Angle.op C i.1 j.1 k.1 u v b))):=by
  simp_rw [Fintype.sum_prod_type]; unfold Angle.op; simp_rw [Finset.mul_sum,Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm (t:=(Finset.univ:Finset P))]; apply Finset.sum_congr rfl; intro l _; rw [log]; unfold fuel; push_cast; ring
-- finish the color trace
lemma sum_t (C:Shade.Cut) (u v b:E4): (∑ m:L,∑ n:L,∑ i:L,∑ j:L,∑ k:L,item C u v b i j k m n)= (↑(answer C G u v b):ℂ):=by -- answer lowercase
  let f:= fun m n i j k:L=> item C u v b i j k m n; calc
    _ = ∑ i:L,∑ j:L,∑ k:L,(∑ m:L,∑ n:L,f m n i j k):= ?_
    _ = _:= ?_
  · conv_lhs=> enter [2,m]; rw [Finset.sum_comm]; skip
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; conv_lhs=> enter [2,m]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; conv_lhs=> enter [2,m]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  unfold f; simp_rw [dross, ← Complex.ofReal_sum]; refine congr_arg _ ?_; -- reorder
  unfold answer; rw [show 6 * S_color G * tens C u v b= (∑ i:Υ,∑ j:Υ,∑ k:Υ, ∑ m:P,∑ n:P,∑ p:P,(6*br i j k^2)*(liftedSign m n p*Angle.op C m n p u v b)) from ?_] ; simp_rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset P)) (t:=(Finset.univ:Finset Υ))]; unfold S_color tens; rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, Finset.sum_mul]; simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset P)) (t:=(Finset.univ:Finset Υ))]
private abbrev priceH (i j k m n:L)(x y z:Cover): ℂ:=6*fuel i j k * bstep W g x j (u_line g W y m)* bstep W g x k (u_line g W z n)*trioW W g x y z i m n
include p in
private lemma beat (i j k m n:L)[F.IsCountablyGenerated][NeBot F]: Named F a 14 (fun w=> priceH W g i j k m n (x w) (y w) (z w)) (item C u v b i j k m n) :=by
  unfold item; have he:= ((((Player.quoted (M j) (Y m) g p).const_mul (6*fuel i j k)).mul (quoted (M k) (Y n) g p.hop.turn)).mul (tri_at W g p i m n)); exact he
include p in
lemma sure [F.IsCountablyGenerated][NeBot F]: Named F a 14 (fun i=> Seal W g (x i) (y i) (z i)) ↑(answer C G u v b):=by
  rw [← sum_t C]; simp_rw [sealed, playAll,scoreX]; exact Named.sum _ _ _ (fun m (_:m∈Finset.univ)=> Named.sum _ _ _ (fun n (_:n∈Finset.univ)=>Named.sum _ _ _ (fun i (_:i∈Finset.univ)=>Named.sum _ _ _ (fun j (_:j∈Finset.univ)=>Named.sum _ _ _ (fun k (_:k∈Finset.univ)=> beat W g p i j k m n)))))
end YM.XSpace.Finale
