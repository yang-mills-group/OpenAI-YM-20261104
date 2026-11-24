import YM.OPE.Compatible.Frog.Bund
/-!
# thermal scaling in axes, Pedestal. stand-alone and vertical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Pose
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Bloch Precision Wilson Exterior Flume Flume.Virgin Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Arc Stranded Adhesion Silt
open Shell Char Module Finset
variable {F E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
local notation "N!"=> finrank ℝ E
-- one angular derivative charge. E finite any.
abbrev normE (x:E):ℝ:= L.P x x
abbrev hillP (p:E→ℝ)(x:E):ℝ:= fderiv ℝ p x x
lemma foretell (p:E→ℝ)(hp:Bond p):
     L.average μ (normE L*p)= N!*L.average μ p + L.average μ (hillP p):=by
         let B:= finBasis ℝ E; let u(i):= ⇑(B.coord i); let d(i:Fin N!)(x:E):ℝ:= u i x*fderiv ℝ p x (B i)
         have he(y:E):y=∑ i,u i y • B i := (B.sum_repr y).symm; let f:E→ℝ:=∑ i,(⇑(L.P (B i)))*(u i*p)
         rw [show normE L*p=f from ?_,show hillP p=(∑ i,d i) from ?_]; rotate_left
         · funext i; rw [Finset.sum_apply]; unfold hillP; nth_rw 2 [he i]; rw [map_sum]; refine sum_congr rfl fun j _=>?_ ; rw [map_smul];rfl
         · funext i; rw [show f i= _ from Finset.sum_apply i _ _,Pi.mul_apply]; unfold normE; nth_rw 1 [he i]; rw [map_sum,LinearMap.sum_apply,Finset.sum_mul]; refine Finset.sum_congr rfl ?_; intro j _; rw [map_smul,LinearMap.smul_apply, show (⇑(L.P (B j))*(u j*p)) i=_ from rfl]; change u j i * _ * _ = L.P _ _*(u j i*p i);ring
         have hd (i):Bond (d i):=(Bond.glyph (B.coord i)).mul (hp.amount _)
         have ht(i:Fin N!):L.average μ (⇑(L.P (B i)) * (u i*p))= L.average μ p + L.average μ (d i):=by
              rw [← sun μ L hp (hd i)]; refine bask μ L (B i) (u i*p) (p+d i) ((Bond.glyph (B.coord i)).mul hp) (hp.add (hd i)) (fun a t=>?_)
              let v(t:ℝ):= a+t • B i; have hv:HasDerivAt v (B i) t:=by simpa [v] using! ((hasDerivAt_id' t).smul_const (B i)).const_add a
              let U:= (B.coord i).toContinuousLinearMap; convert! ((U.hasFDerivAt.comp_hasDerivAt t hv).mul ((hp.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp_hasDerivAt t hv)) using 1
              change p _+u i _* _= U (B i) *_+ _; rw [show U (B i)=1 from by change B.coord i (B i)=_; simp,one_mul];rfl -- verify
         unfold f; rw [science μ L univ _ ?_, science μ L univ _ (fun i _=> hd i)]; simp_rw [ht,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]; exact fun i _=> (Bond.glyph (L.P _)).mul ((Bond.glyph (B.coord i)).mul hp)
lemma fullV : L.average μ (normE L)=(N!:ℝ):=by
      have hp: hillP (1:E→ℝ)=0:=by funext i; unfold hillP; show fderiv ℝ (fun _:E=>(1:ℝ)) i i=0; rw [fderiv_const_apply]; rfl
      simpa only [mul_one, hp,L.empty, show L.average μ 0=0 from singleConst μ L 0,add_zero] using foretell μ L 1 Bond.one
omit [MeasurableSpace E] [BorelSpace E] in lemma standE: Bond (normE L) :=by
    let B:= finBasis ℝ E; rw [show normE L=(fun x:E=>∑ i:Fin N!, (B.coord i x * L.P (B i) x)) from ?_]; exact Bond.sum _ univ (fun i _=> (Bond.glyph (B.coord i)).mul (Bond.glyph (L.P _)))
    funext i; unfold normE; nth_rw 1 [← B.sum_repr i]; rw [map_sum,LinearMap.sum_apply]; exact sum_congr rfl (fun j _=>by rw [map_smul,LinearMap.smul_apply];rfl)
omit [MeasurableSpace E] [BorelSpace E] in lemma heatE {p:E→ℝ}(hp:Bond p):Bond (hillP p):=by let B:= finBasis ℝ E; rw [show hillP p=(fun i=>∑ j:Fin N!,B.coord j i * fderiv ℝ p i (B j)) from ?_]; exact Bond.sum _ univ (fun j _=> (Bond.glyph (B.coord j)).mul (hp.amount _)); funext i; unfold hillP; nth_rw 2 [← B.sum_repr i]; rw [map_sum]; exact sum_congr rfl (fun j _=>by rw [map_smul];rfl)
end YM.OPE.Libra.Pose
