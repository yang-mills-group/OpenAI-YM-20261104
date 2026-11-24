import YM.WilsonBridge.Exponent

/-!
# Wick calculus in different bases

Uses the concrete `YM.MS.Cylinder` finite stencil and Fourier-evaluation algebra. The
covariance hypothesis is a *pushforward*, not an inverse relation. Covers singular
inversion-image covariances as well as decoupled/reprojected unphysical letters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Native MS.Puff MS.Cylinder MS.Orbit
open Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Orbit.LogReal Orbit.Cog Book.Convolve
open Function Finset
open scoped BigOperators Matrix
variable {V K H : Type} [Fintype V] [Fintype K] [Fintype H] {q : Sector V} {r : Sector K}
variable (U : Matrix K V ℂ) (W : Matrix H K ℂ) {F : Raw V ℂ}
-- finite `pull` matrix U indexed [target alphabet,source alphabet].
-- Matrix and 2-arg notation intentionally both.
abbrev pull (U : Matrix K V ℂ): Linear (Raw V ℂ) (Raw K ℂ) := lantern Finset.univ U
omit [Fintype K] in
@[simp] lemma pull_nil : pull U F []=F []:= rfl
omit [Fintype K] in
lemma pull_drop (j:K) : D j (pull U F)=∑ i:V,U j i • pull U (D i F):= lantern_drop U _ _
omit [Fintype K] in
lemma pull_is_shade (F:Cyl V ℂ): pull U F.val=shade (fun i j=> U i j) F:= (tinted _ F (by rw [Finset.coe_univ]; exact Uses.entire _)).symm
omit [Fintype K] in
lemma pull_ink {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (N:Matrix K V ℝ) (Z:V→E) (Y:K→E)(L : E→ℝ) (h:Taylor.germ L) (he:∀ i, Y i=∑ j,N i j • Z j): pull (N.map ((↑) : ℝ→ℂ)) (Taylor.ink Z L)=Taylor.ink Y L:= by
  rw [Taylor.scale_pos Z Y N he h]; exact pull_is_shade (N.map ((↑) : ℝ→ℂ)) (region.symm (Taylor.ink Z L))
omit [Fintype K] in
lemma pull_prod (h:Tie q r (fun i j=>U i j)) (F G: Raw V ℂ) : pull U (product q F G)=product r (pull U F) (pull U G):= by
  change pull U (couple q (region.symm F) (region.symm G)).val=product r (pull U (region.symm F).val) (pull U (region.symm G).val)
  simp_rw [pull_is_shade]; exact h.prod ..
omit [Fintype K] in
lemma pull_mask (v:ℤ): pull U (mask v F)=mask v (pull U F):= by
  change pull U (model v (region.symm F)).val=mask v (pull U (region.symm F).val)
  simp_rw [pull_is_shade]; exact mod_ink _ _
omit [Fintype K] in
lemma pull_from {m:ℤ} (h : From F m): From (pull U F) m:= by
  intro l he; rw [← enough l (F:=pull U F) rfl,← pull_mask,show mask (l.length:ℤ) F=0 from ?_,map_zero]; · rfl
  funext v; by_cases hh:(v.length:ℤ)=(l.length:ℤ); · exact (enough _ hh).trans (h v (by omega))
  exact strange _ hh
omit [Fintype K] in
lemma pull_limit {m:ℤ} (h : Limit F m): Limit (pull U F) m:= by
  rw [show pull U F=_ from pull_is_shade U (region.symm F)]; exact Limit.shades _ h _
omit [Fintype K] in
lemma pull_symm (h:Tie q r (fun i j=>U i j)) (hF:MS.Koszul.Symm q F) : MS.Koszul.Symm r (pull U F):= by
  rw [show pull U F=_ from pull_is_shade U (region.symm F)]; exact h.sym _ hF
lemma pull_letter (i:V) : pull U (atLetter i)=∑ j:K,U j i • atLetter j:= by
  classical
  apply ext_D
  · rw [Finset.sum_apply, Finset.sum_eq_zero]; rfl; exact fun _ _=> mul_zero _
  intro j; rw [ pull_drop, Finset.sum_eq_single_of_mem i (mem_univ i), hear ]; swap; · exact fun k hk h=>by rw [unheard i h,map_zero,smul_zero]
  simp_rw [map_sum,map_smul]; rw [Finset.sum_eq_single_of_mem j (mem_univ j), hear ]; swap; · exact fun k hk h=>by rw [unheard k h.symm,smul_zero]
  rw [show pull U (coin 1)=_ from Eq.trans (pull_is_shade U (piece (1:ℂ))) ( coin_turn .. )] -- defeq?
omit [Fintype H] in
lemma pull_comp : pull W (pull U F)=pull (W*U) F:= by
  funext l; induction l generalizing F with
    | nil=> rfl
    | cons i l ih=>
      rw [D_eval i (pull W _),pull_drop,D_eval i (pull _ F),pull_drop]; simp_rw [pull_drop,map_sum,map_smul, Finset.smul_sum, Finset.sum_apply,Pi.smul_apply,ih]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=>?_; rw [Matrix.mul_apply,Finset.sum_smul]; simp_rw [mul_smul]
lemma pull_id [DecidableEq V] : pull (1:Matrix V V ℂ) F=F:= by
  funext l; induction l generalizing F with| nil=>rfl | cons i l ih=> rw [D_eval i (pull _ F),pull_drop]; simp only [Matrix.one_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,if_true, ih, at_D]

omit [Fintype K] in
lemma pull_one (c:ℂ): pull U (coin c)=coin c:= Eq.trans (pull_is_shade U (piece c)) (coin_turn ..)

def cov_push (P : Grain K) (U : Matrix K V ℂ) : Grain V := (U.transpose * Matrix.of P) * U
omit [Fintype V] in
lemma entries (P:Grain K)(i j:V): cov_push P U i j=∑ a:K,∑ b:K, U a i*P a b*U b j:= by
    unfold cov_push; rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply, Finset.sum_mul]; exact Finset.sum_comm
lemma frame_pull {R : Grain K}{P : Grain V}(he: cov_push R U=P) : frame R (pull U F)=pull U (frame P F):= by
  subst P; simp_rw [fpΩ,diffPair_apply,pull_drop,map_sum,map_smul,pull_drop]
  simp_rw [Finset.smul_sum, entries U, Finset.sum_smul,smul_smul]
  have S (f: K→ K→V→V→Raw K ℂ):
      (∑ i,∑ j,∑ u,∑ v,f i j u v) = ∑ u,∑ v,∑ i,∑ j,f i j u v:= by
    simp_rw [show ∀ i, (∑ j,∑ u,∑ v, f i j u v)= ∑ u,∑ v,∑ j,f i j u v from
      fun i=> (Finset.sum_comm).trans (Finset.sum_congr rfl fun u _=> Finset.sum_comm)]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _=>?_ ; rw [Finset.sum_comm]
  simp_rw [mul_assoc]
  rw [S (fun i j u v=>(R i j*(U i u*U j v)) • (pull U (D v (D u F))))]
  refine Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=>?_ ; congr 1; ring
lemma pux_shot {R : Grain K}{P : Grain V}(he: cov_push R U=P){n : ℕ} (hz: Limit F n): Shot R (pull U F)=pull U (Shot P F):= by
  have hm (n:ℕ) : tep R n (pull U F)= pull U (tep P n F):= by
    induction n with | zero=> rw [rise,rise]; rfl| succ n ih=> rw [teen, ih, teen, frame_pull U he,map_smul]
  rw [dawn R (pull_limit U hz),dawn P hz,effect,effect]; simp_rw [LinearMap.sum_apply,map_sum,hm]
lemma pull_view {R : Grain K}{P : Grain V}(he: cov_push R U=P) (hz:F∈ Mini V): View R (pull U F)=View P F:= by
  obtain ⟨n,h⟩:= hz; change Shot R _ []=_; rw [pux_shot U he h]; rfl
omit [Fintype K] in
lemma tether (h:Tie q r (fun i j=>U i j)): Tether (pull U) (actor q) (actor r):= ⟨pull_one ..,pull_prod _ h⟩
omit [Fintype K] in
lemma pull_C (h:Tie q r (fun i j=>U i j)) (Q V : T (Raw V ℂ)):
    pointL ℕ (pull U) ((PermV q).core Q V)= (PermV r).core (pointL ℕ (pull U) Q) (pointL ℕ (pull U) V) :=
  ( (tether U h).Extrapolation useN).craft _ _
omit [Fintype K] in
lemma pull_exp (h:Tie q r (fun i j=>U i j)) (Q : T (Raw V ℂ)):
    pointL ℕ (pull U) (exp0 q Q)= exp0 r (pointL ℕ (pull U) Q):=
  funext fun i=> (tether U h).figure useN Q i
lemma shade_view {R : Grain K}{P : Grain V}(he: cov_push R U=P) {Q: T (Raw V ℂ)} (hQ:Γ Q q) : ℶV R (pointL ℕ (pull U) Q)=ℶV P Q:= funext fun i=> pull_view U he (fee_spec (hQ i (Set.mem_univ _))).2
lemma pull_end (Q X : T (Raw V ℂ)) {R : Grain K}{P : Grain V}(he: cov_push R U=P)
    (hQ : Γ Q q)(hX : Γ X q)(h:Tie q r (fun i j=> U i j))(Z) :
    Endμ R r (pointL ℕ (pull U) Q) (pointL ℕ (pull U) X) Z ↔ Endμ P q Q X Z:= by
    unfold Endμ
    rw [← pull_exp U h,← pull_C U h, shade_view U he ( ΤΓ_pair (expΓ hQ) hX),shade_view U he (expΓ hQ)]
end YM.WilsonBridge
