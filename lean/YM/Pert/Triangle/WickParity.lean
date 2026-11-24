import YM.Pert.Parity.Fields
import YM.Pert.Scale.Circuit
/-! Parity of the leading actual Maxwell moments by Wick matching, not requiring a Stokes or gauge change. Simultaneous potential sign, not a CPT assumption. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedVariables false
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Matrix Filter TopologicalSpace MeasureTheory Wick Parity Wick.Occ
open scoped ContDiff Topology RealInnerProductSpace Classical
variable {G:Gauge}
def reversePol (G:Gauge) : WickPol G→ₐ[ℂ] WickPol G := MvPolynomial.aeval fun s => -MvPolynomial.X s
lemma reverse_read (A : TaylorTower G) (p:WickPol G) : Maxwell.probe A (reversePol G p) = Maxwell.probe (-A) p := by
  have : (Maxwell.probe A).comp (reversePol G)=Maxwell.probe (-A) := by ext; simp only [AlgHom.comp_apply,reversePol, MvPolynomial.aeval_X,map_neg,Maxwell.probe,coord,Pi.neg_apply,Finsupp.neg_apply, Complex.ofReal_neg]
  exact DFunLike.congr_fun this p
-- replace with tower names
lemma reversal_raw (p : Labels.Pol G) : reduceEq (Parity.shadow G p) = reversePol G (reduceEq p) := by
  apply Maxwell.equalPol
  intro q
  rw [Maxwell.jet_value,reverse_read,Maxwell.jet_value,Parity.shadow_read]
  congr 2; funext i; exact (map_neg (gaugeJet (G:=G) (j:=i)) _).symm

lemma reverse_basis (w : Slot G→₀ℕ) : reversePol G ((monBasis G) w) = (-1:ℂ)^(∑j∈w.support,w j) • monBasis G w := by
  change reversePol G (MvPolynomial.monomial w 1) = (_:ℂ) • MvPolynomial.monomial w (1:ℂ)
  rw [MvPolynomial.monomial_eq,_root_.map_mul,Finsupp.prod,_root_.map_prod, MvPolynomial.smul_eq_C_mul]
  simp only [reversePol,_root_.map_pow,MvPolynomial.aeval_X, neg_eq_neg_one_mul (MvPolynomial.X _ :WickPol G), mul_pow]
  rw [Finset.prod_mul_distrib]
  have h : (∏j∈w.support,(-1:WickPol G)^(w j)) = ((-1:WickPol G)^(∑j∈w.support,w j)) := Finset.prod_pow_eq_pow_sum ..
  simp only [h,map_neg,map_one,mul_assoc,one_mul,mul_one]

lemma eventally_even_count {m} (W:Powers G m) (P:Occ.Matching W) : Even (∑i,∑ j∈(W i).support,W i j) := by
  classical
  have hw : Occ.partner P * Occ.partner P = 1 := P.property.1
  have hd := fun i=> Occ.different P i
  have flip (i:Occ W) : Occ.partner P i∈Occ.corners P ↔ i∈ Finset.univ \ Occ.corners P := (Occ.orientation P i).trans (by simp)
  have he : Finset.card (Occ.corners P) = Finset.card (Finset.univ \ Occ.corners P) := by
     apply Finset.card_bij (fun i _=> Occ.partner P i)
     · exact fun a ha => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h=> ((Occ.orientation P a).mp h) ha⟩
     · exact fun _ _ _ _ e => (Occ.partner P).injective e
     exact fun b hb=> ⟨Occ.partner P b, (flip b).mpr hb, Occ.turn P b⟩
  have hc : Fintype.card (Occ W)=∑i,∑j∈(W i).support,W i j:= by
    rw [Fintype.card_congr Scale.ranks]
    simp only [Fintype.card_sigma,Fintype.card_fin]
    exact Finset.sum_congr rfl (fun i _=> Finset.sum_attach (W i).support (fun j=> W i j))
  have hi := Finset.card_sdiff_add_card_eq_card (show Occ.corners P ⊆ Finset.univ from Finset.subset_univ _)
  rw [←hc, ←Finset.card_univ]
  exact ⟨Finset.card (Occ.corners P),by omega⟩
lemma anti_relabel (G:Gauge) (m:ℕ) (x:Points m) :
     (Wick.moment G x).compLinearMap (fun _:Fin m=> reversePol G |>.toLinearMap) = Wick.moment G x := by
  classical
  ext1 p
  rw [Multilabel.expansion (fun _ : Fin m => monBasis G), Multilabel.expansion (fun _=> monBasis G) (Wick.moment G x)]
  apply Finset.sum_congr rfl; intro W _
  congr 1
  change Wick.moment G x (fun i=>reversePol G (monBasis G (W i))) = _
  simp_rw [reverse_basis,MultilinearMap.map_smul_univ,smul_eq_mul,moment_basis, monomial, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun P _=>by rw [Finset.prod_pow_eq_pow_sum, (eventally_even_count W P).neg_one_pow, one_mul])
lemma Wick_flip {m} (G:Gauge) (x:Points m) (p:Fin m→WickPol G) :
    Wick.moment G x (reversePol G ∘ p) = Wick.moment G x p :=
  congrArg (fun v:MultilinearMap ℂ (fun _:Fin m=>WickPol G) ℂ=>v p) (anti_relabel G _ x)
end YM.Pert.Triangle
