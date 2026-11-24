import YM.SchemeRG11.Wisp.Osc
import YM.SchemeRG11.Plate.Aero
import YM.SchemeRG11.Saddle.Top
/-! Landau stencils receive the same invariant columns even WITH Wick shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius PowerSeries
open Function Filter Lattice MeasureTheory Pert Pert.Orb Lam PertExtension.Chart
open Haze Atoll North Pile Labels MvPolynomial
variable {G:Gauge}{n:Side}
abbrev chipC (u:G.El)(p:Key G): Stem (Key G) ℂ:= ∑ i,Finsupp.single (⟨p.1,i⟩:Key G) (((axes G p.1).coord p.2 (Taylor.paint u ((axes G p.1) i))):ℂ)
lemma hmark(h:ℝ)(i j:Key G): (Atoll.unmarked G h).pulse i j= pad h i*pad h j*(Atoll.unmarked G 1).pulse i j:=by unfold Atoll.unmarked Dose.pull leafProbe; simp only [one_zpow,one_smul, pad_eq,colour_thin]
lemma moved_pull (u:G.El)(h:ℝ):
    let L: Dose (Key G) ℂ:= (Atoll.unmarked G h).mapped Complex.ofRealHom
    L.pull (chipC u)=L:=by
 intro L; apply Dose.strict; intro i j
 have hs:=tropic i j u
 let cM(k:Key G)(v:Fin (dim G k.1)):= (axes G k.1).coord k.2 (Taylor.paint u ((axes G k.1) v))
 change _ = (Atoll.unmarked G 1).bed (chip u i) (chip u j) at hs; unfold Dose.bed chip sense at hs
 rw [map_sum] at hs; simp only [Dose.windfall,map_sum,Finsupp.linearCombination_single,Finset.sum_apply, Pi.smul_apply,smul_eq_mul] at hs
 change L.bed (chipC u i) (chipC u j)= _
 unfold L Dose.bed chipC sense; simp only [Dose.windfall,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Dose.mapped, Pi.smul_apply,smul_eq_mul,Complex.ofRealHom_eq_coe,←Complex.ofReal_mul,←Complex.ofReal_sum]
 apply congrArg Complex.ofReal
 simp_rw [hmark h]; conv_rhs => rw [hs]
 change (∑ l, cM j l * ∑ k,cM i k * _)= _; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro z _; unfold cM
 rw [show pad h (⟨j.1,w⟩:Key G)=pad h j from rfl, show pad h (⟨i.1,z⟩:Key G)=pad h i from rfl]; ring

lemma chipC_eq (u:G.El): Haze.vary (chipC u)= changed fun _=>Taylor.paint u:=by
 ext1 i; rw [vary_X,changed,aeval_X]; unfold leaf chipC; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [Finsupp.linearCombination_single,C_mul']; rfl
lemma change_inv {p:Pol G}(h:p∈ invariantSpace G)(u:G.El): Labels.changed (fun _=>Taylor.paint u) p=p:= by
 apply Labels.eval_ext; intro A; rw [eval_changed]; exact h A u
lemma dream_inv{p:Pol G}(hp:p∈ invariantSpace G)(h:ℝ): dream h p∈invariantSpace G:=by
 intro A u; unfold dream
 let L:= (Atoll.unmarked G h).mapped Complex.ofRealHom
 rw [← Dose.mapped_neg]; change read (changedJet (fun _=>Taylor.paint u) A) (L.neg.heat p)=_
 rw [← eval_changed,← chipC_eq]; rw [show Haze.vary (chipC u) (L.neg.heat p)=L.neg.heat (Haze.vary (chipC u) p) from by rw [Dose.night, moved_pull u h],chipC_eq,change_inv hp u]
lemma waist(u:G.El)(p: Pol G)(k:ℕ): Labels.changed (fun _=>Taylor.paint u) (homogeneousComponent k p)= homogeneousComponent k (Labels.changed (fun _=>Taylor.paint u) p):=by
 let L:=Labels.changed (fun _=> Taylor.paint u)
 have h(i: Key G→₀ ℕ)(c:ℂ): L (homogeneousComponent k (monomial i c))= homogeneousComponent k (L (monomial i c)):=by
    have hm: (monomial i c).IsHomogeneous i.degree:= isHomogeneous_monomial c rfl
    have hh: IsHomogeneous (Labels.changed (fun _=> Taylor.paint u) (monomial i c)) i.degree:=by
      have hx:=Labels.pure_moved (fun _=>1) (fun _=>Taylor.paint u) i c
      rw [Finsupp.degree_eq_weight_one]; exact hx
    unfold L; rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hh]; split <;> simp
 conv_lhs=> rw [← p.support_sum_monomial_coeff]
 conv_rhs=> rw [← p.support_sum_monomial_coeff]
 change L _ = homogeneousComponent k (L _); simp only [_root_.map_sum]; apply Finset.sum_congr rfl; exact fun i _=> h i _
lemma homogeneous_inv {p:Pol G}(hp:p∈ invariantSpace G)(k:ℕ): homogeneousComponent k p∈invariantSpace G:=by
 intro A u; change read (changedJet (fun _=>Taylor.paint u) A) _=read _ _; rw [← eval_changed, waist,change_inv hp]
end YM.SchemeRG11.Sway
