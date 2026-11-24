import YM.XSpace.TopLabel
/-!
# The Wick-jet change of frame on exact stencils

Taking inverse, also handle unit grade and real-even input constraints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson Source Source.Drops MeasureTheory
open Next.Rank Normal Spindle Beamer Next.Foundations Configuration MvPolynomial LiftMark
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical

section shrink
variable {V S : Type*}
private lemma narrow (F : Finset S) (f : S → V) : totalDegree (glyphs f F) ≤ F.card := by
  exact (totalDegree_finsetProd ..).trans (by simp)

lemma reduction (Q : Symmetric V) (F : Finset S) (f : S→V): totalDegree (milk Q (glyphs f F)-glyphs f F) ≤ F.card-1 := by
  induction F using Finset.strongInduction with
  | H F ih =>
    by_cases h:F=∅; · simp [h]
    obtain ⟨v,hv⟩:= Finset.nonempty_iff_ne_empty.mpr h
    let J := F.erase v
    have he:v∉J:= Finset.notMem_erase _ _
    have hh:F=insert v J:= (Finset.insert_erase hv).symm
    have hJ : J ⊂ F := Finset.erase_ssubset hv
    by_cases hp : J=∅
    · rw [hh,hp]
      unfold glyphs; simp only [Finset.prod_insert (Finset.notMem_empty v)]
      rw [Finset.prod_empty,Normal.feeds,pure,(slit _).map_one_eq_zero]; simp
    rw [hh,Finset.card_insert_of_notMem he, Nat.add_sub_cancel]
    have hx : glyphs f (insert v J)= X (f v)*glyphs f J:= Finset.prod_insert he
    rw [hx,Normal.feeds,Normal.skims]
    let L:= Normal.slit (Q.cov (f v)); let X₀: poly V:= MvPolynomial.X (f v)
    let g:= glyphs f J
    have hz : X₀*milk Q g+milk Q (L g)-X₀*g=X₀*(milk Q g-g)+milk Q (L g):= by ring
    rw [hz]; refine (totalDegree_add ..).trans (max_le ?_ ?_)
    · refine (totalDegree_mul ..).trans ?_
      have hi:= ih J hJ; change totalDegree (MvPolynomial.X (R:=ℂ) (f v))+totalDegree (milk Q (glyphs f J)-glyphs f J) ≤ _; rw [totalDegree_X]; have hv : 0<J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp); exact (Nat.add_le_add_left hi 1).trans_eq (by omega)
    unfold L g; rw [Normal.renew, map_sum]; simp_rw [map_smul]
    apply totalDegree_finsetSum_le; intro j hj
    refine (totalDegree_smul_le ..).trans ?_
    let Y:= J.erase j; let y:= glyphs f Y
    have hi: totalDegree (milk Q y)≤ Y.card := by
      conv_lhs=> rw [show milk Q y=(milk Q y-y)+y by ring]
      exact (totalDegree_add ..).trans (max_le ((ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hJ)).trans (Nat.sub_le _ _)) (narrow Y f))
    exact hi.trans (Finset.card_le_card (Finset.erase_subset ..))

lemma strict_brew (P : poly V) (Q : Symmetric V): totalDegree (milk Q P-P) ≤ P.totalDegree-1 := by
  conv_lhs => rw [P.as_sum,map_sum,← Finset.sum_sub_distrib]; skip
  apply totalDegree_finsetSum_le; intro i hi
  rw [MvPolynomial.monomial_eq, C_mul', map_smul,← smul_sub]; apply (totalDegree_smul_le ..).trans
  let S := (v : i.support) × Fin (i v.val)
  let Z (a:S):= a.1.val
  have he : i.prod (fun j n=> (X j:poly V)^n)=glyphs Z Finset.univ:= by rw [Finsupp.prod,← Finset.prod_attach,glyphs,Fintype.prod_sigma]; simp [Z]
  rw [he]; apply (reduction Q (Finset.univ:Finset S) Z).trans
  apply Nat.sub_le_sub_right
  simp only [Finset.card_univ,S,Fintype.card_sigma, Fintype.card_fin, Finset.univ_eq_attach,Finset.sum_attach i.support (fun x=>i x)]; exact le_totalDegree hi
end shrink
variable {G : Gauge} {d:ℕ}
lemma polyCount (i : Index G d) : totalDegree (ground (chosen i))≤ glyphCount i:= by
  apply (totalDegree_rename_le ..).trans
  apply totalDegree_finsetSum_le; intro v hv
  split
  next h => exact (totalDegree_monomial_le ..).trans_eq h
  simp

lemma W_unit (G : Gauge) (d : ℕ) : W0 G d (Frame G d).e0=(Frame G d).e0 := by
  let i : Index G d:=0
  let p := ground (chosen i)
  have he: p.totalDegree=0:= Nat.eq_zero_of_le_zero (show p.totalDegree≤0 by simpa only [p, glyphCount, i,Labels.Frame.zero_degree] using polyCount i)
  have hp : milk (WickK G) p=p := by rw [totalDegree_eq_zero_iff_eq_C.mp he]; simp
  have hh : LabelW G d (Pi.single i 1)= (Frame G d).basis i:= by
    apply Subtype.ext
    change (rename (Subtype.val:_→_)) (Pi0 G d (milk (WickK G) (letters G d (Pi.single i 1))))=_
    rw [canonical_expr, hp]; unfold p; rw [pi_leading,Configuration.returns]
  change (Frame G d).coords (LabelW G d (Pi.single i 1))=_; rw [hh]; exact Labels.Frame.coords_basis ..

lemma charge (i : Index G d): totalDegree (LabelW G d (Pi.single i 1) - (Frame G d).basis i).val ≤ glyphCount i-1:= by
  let p:= ground (chosen i)
  let Φ:= (rename (Subtype.val : KeyIn G d→Labels.Key G)).toLinearMap.comp (Pi0 G d)
  have hp: Φ p=((Frame G d).basis i).val:=by unfold Φ p; simp only [LinearMap.comp_apply]; rw [pi_leading]; exact Configuration.returns ..
  change totalDegree (Φ (milk (WickK G) (letters G d _))-_)≤_
  rw [canonical_expr, ← hp, show ground (chosen i)=p from rfl,← _root_.map_sub]
  exact (totalDegree_rename_le ..).trans ((Rise.below_degree ..).trans ((Rise.ascent ..).trans ((strict_brew p _).trans (Nat.sub_le_sub_right (polyCount _) _))))

lemma pay_coords (P : Labels.Label G d) (i : Index G d) (h : totalDegree P.val < glyphCount i): (Frame G d).coords P i=0 := by
  let F:=Frame G d; let m:= F.grades i
  have he := Labels.decompose P
  nth_rw 1 [← he]; simp_rw [map_sum,Finset.sum_apply]; refine Finset.sum_eq_zero fun u _=> Finset.sum_eq_zero fun v _=> ?_
  by_cases hx : m=(u,v)
  · have hx : Labels.gradePart (u,v) P=0 := by
      rw [← hx]
      apply Subtype.ext
      change (weightedHomogeneousComponent Labels.bidegree m P.val) = 0
      ext1 b; rw [coeff_weightedHomogeneousComponent]; simp only [coeff_zero]; split
      next hg => exact coeff_eq_zero_of_totalDegree_lt (h.trans_eq (by rw [Labels.weight_slot] at hg; exact (congr_arg Prod.snd hg).symm))
      rfl
    rw [hx,map_zero]; rfl
  exact F.power_coefficient _ (Ne.symm hx) (Labels.gradePart_mem (u,v) P)

theorem decreasing (i j : Index G d) (h : glyphCount i ≤ glyphCount j): (W0 G d (Pi.single i 1)-Pi.single i 1 : (Frame G d).Coeff) j = 0:= by
  by_cases he:i=0; · rw [he, show W0 G d (Pi.single 0 1)=Pi.single 0 1 from W_unit G d]; simp
  let F:=Frame G d
  have hv : totalDegree (LabelW G d (Pi.single i 1)-F.basis i).val<glyphCount j := by refine lt_of_le_of_lt (charge _) ?_; exact lt_of_lt_of_le (Nat.sub_lt (F.factors_pos i he) one_pos) h
  have hp:= pay_coords _ _ hv; rw [map_sub,Labels.Frame.coords_basis] at hp; exact hp

-- inverse without sorting: span induction from the grade rows
lemma W_onto (G : Gauge) (d : ℕ): Surjective (W0 G d):= by
  let R:= LinearMap.range (W0 G d)
  have he (k:ℕ) (i:Index G d) (hi:glyphCount i=k) : (Pi.single i (1:ℂ))∈ R := by
    induction k using Nat.strong_induction_on generalizing i with
    | h k ih =>
      let P : (Frame G d).Coeff:= Pi.single i 1
      let Q:= W0 G d P
      have hp:Q-P ∈ R := by
        rw [coord_sum (Q-P)]; apply Submodule.sum_mem; intro j hj; by_cases h:glyphCount i ≤ glyphCount j
        · rw [show (Q-P) j=0 from decreasing i j h, zero_smul]; exact R.zero_mem
        exact R.smul_mem _ (ih _ (lt_of_lt_of_le (lt_of_not_ge h) hi.le) _ rfl)
      rw [show Pi.single i 1 = Q-(Q-P) by change P= _; abel]; exact R.sub_mem ⟨P,rfl⟩ hp
  intro p; suffices p ∈ R from this
  rw [coord_sum p]; exact Submodule.sum_mem _ fun i _=> R.smul_mem _ (he _ i rfl)

def W (G : Gauge) (d:ℕ) := LinearEquiv.ofBijective (W0 G d) ⟨LinearMap.injective_iff_surjective.mpr (W_onto G d),W_onto G d⟩
lemma inv_W (p:(Frame G d).Coeff): W0 G d ((W G d).symm p)=p := (W G d).apply_symm_apply _

lemma W_inv_u (G : Gauge) (d:ℕ) : (W G d).symm (Frame G d).e0 = (Frame G d).e0:= (LinearEquiv.symm_apply_eq (W G d)).mpr (W_unit G d).symm
lemma W_inv_s (p:(Frame G d).Coeff) : (W G d).symm (star p)=star ((W G d).symm p):= by
  apply (LinearEquiv.symm_apply_eq (W G d)).mpr; rw [show W G d _=W0 G d (star ((W G d).symm p)) from rfl, W0_real,inv_W]
lemma W_inv_h (s:Signed) (p:(Frame G d).Coeff): (W G d).symm ((Frame G d).act s.ortho p)= (Frame G d).act s.ortho ((W G d).symm p):= by
  apply (LinearEquiv.symm_apply_eq (W G d)).mpr; rw [show W G d _=W0 G d ((Frame G d).act _ ((W G d).symm p)) from rfl, W0_H, inv_W]

lemma pure_jet (P : Labels.Label G d): Pi0 G d (choiceW G d ((W G d).symm ((Frame G d).coords P)))=thawKey P := by
  apply rename_injective (R:=ℂ) (f:=Subtype.val) Subtype.val_injective; rw [Configuration.returns]; exact congr_arg Subtype.val ((Frame G d).coords.injective (inv_W _))
end YM.XSpace
