import YM.SchemeRG11.Plate.Atmosphere
import YM.SchemeRG11.Cover.Shear
/-! Order-by-order identity of proposed scheme stencils with the Full Wilson PT ground rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Atoll
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology BigOperators
variable {G : Gauge} {N : Side} {j:ℕ}
abbrev leafProbe(h:ℝ)(i: Key G): Touch G:= h^(-(i.1+2:ℤ)) • alpha (0:Cover) i.1 ((axes G _).coord i.2)
def unmarked(G:Gauge)(h:ℝ): Dose (Key G) ℝ:= (land G).pull (leafProbe h)
lemma unmasked(h:ℝ)(i j:Key G): (unmarked G h).pulse i j= Full.link h i j:= Eq.symm (nightfall ..)
def inkD (G:Gauge)(d:ℕ)(h:ℝ): Dose (Key G) ℂ where
 pulse p q := if p.1≤d ∧ q.1≤d then - (link h p q:ℂ) else 0
 beats p q:=by simp only [Full.link_symm h p q,and_comm]

def inkLine (d:ℕ)(p:Key G): Aux G d→L[ℝ] ℂ:= if hp:p.1≤d then Complex.I • Complex.ofRealCLM ∘L (Warp.guest ⟨p,hp⟩) else 0 -- adjust
lemma inkHost(d:ℕ)(p:Key G)(v:Aux G d): inkLine d p v= Full.ink v p:=by
 unfold inkLine ink; split
 · rfl
 simp
lemma inkStats(d:ℕ)(p q:Key G)(h:ℝ): ∫ x,ink x p*ink x q ∂auxLaw G d h=(inkD G d h).pulse p q:=by
 by_cases hp:p.1≤d<;> by_cases hq:q.1≤d
 · have he (v:Aux G d): Full.ink v p* Full.ink v q= - (↑(Warp.guest (⟨p,hp⟩:CosKey G d) v * Warp.guest (⟨q,hq⟩:CosKey G d) v):ℂ):=by simp only [Full.ink,hp,hq,↓reduceDIte]; push_cast; change Complex.I * _ * (Complex.I * _) = - ((↑(v (⟨p,hp⟩:CosKey G d)):ℂ)* ↑(v (⟨q,hq⟩:CosKey G d))); calc _ = Complex.I^2 * ((↑(v (⟨p,hp⟩:CosKey G d)):ℂ)* ↑(v (⟨q,hq⟩:CosKey G d))) := by ring
                                                                                                                                                                                                                                                                                                                                      _=_:=by simp
   simp_rw [he,integral_neg, integral_complex_ofReal, Warp.guest_quad]; unfold inkD; simp only [hp,hq,and_self,↓reduceIte]
 all_goals simp [inkD,hp,hq,Full.ink]
lemma inkQuiet(d:ℕ)(p:Key G)(h:ℝ): ∫ x, inkLine d p x ∂auxLaw G d h=0:=by
 simp_rw [inkHost]; unfold Full.ink; split
 next e=> change (∫ x, Complex.I * ↑(Warp.guest (⟨p,e⟩:CosKey G d) x) ∂_)=0; rw [integral_const_mul,integral_complex_ofReal,Warp.guest_mean];simp
 next=> simp
lemma inkDye(d:ℕ)(p: Pol G)(h:ℝ): (∫ x:Aux G d, MvPolynomial.eval (Full.ink x) p ∂auxLaw G d h)=(inkD G d h).avg p:=by
 let D:= inkD G d h; let m:= auxLaw G d h; letI : IsGaussian m:= auxGaussian h
 have H:=cash_products m (inkLine d) (fun i:Key G=>inkQuiet d i h) D (fun i k=>by simp_rw [inkHost]; apply inkStats) p
 rw [cash_eq] at H; simp_rw [value,inkHost] at H; exact H

abbrev Era:=PowerSeries ℂ
abbrev extended (p:Pol G):= map (PowerSeries.C) p
variable (d:ℕ)(h:ℝ)(x: Site N)
lemma vest(p:Pol G): Full.avg h (d:=d) (Full.dye p)=PowerSeries.C ((inkD G d h).avg p):=by
 ext1 n; unfold Full.avg dye; simp_rw [PowerSeries.coeff_mk,PowerSeries.coeff_C]
 split
 · exact inkDye d p h
 rw [integral_zero]
lemma splashed(p q:Pol G)(w: Orb.Coords G N): paint d h x p q w= ((inkD G d h).mapped PowerSeries.C).avg (extended q * Dose.bend (seriesLex h x w) (extended p)):=by
 let D: Dose (Key G) Era:= (inkD G d h).mapped PowerSeries.C
 let J:=Dose.bend (seriesLex h x w)
 induction p using MvPolynomial.induction_on generalizing q with
 | C c=>
   have he : Full.paint d h x (C c) q w= Full.avg h ((fun _:Aux G d=> PowerSeries.C c) * Full.dye q):=by unfold Full.paint; congr 1; funext k; simp [Full.pairEval,mul_comm]
   rw [he,Full.avg_const_mul _ _ _ (Full.dye_ready _),vest]
   change _=D.avg (_ * J (extended _))
   simp only [extended]; rw [ MvPolynomial.map_C, show J (C (PowerSeries.C c))=C (PowerSeries.C c) from J.commutes _,mul_comm _ (C _),C_mul',map_smul]
   exact congrArg (PowerSeries.C c * ·) ((inkD G d h).mapped_avg PowerSeries.C q).symm
 | add p r Hp Hr=> simp only [Full.paint_sum,Pi.add_apply,Hp,Hr,extended,map_add,mul_add]
 | mul_X p i Hp=>
   let L:= J (extended p)
   let Z:= seriesLex h x w i
   rw [paint_x]; simp only [Pi.add_apply, Pi.mul_apply,Hp]
   change D.avg (extended _*L)*Z+D.avg (extended _*L)= D.avg (extended _ * J (extended _))
   simp only [extended,_root_.map_mul,map_mul J, MvPolynomial.map_X]
   rw [show J (X i)= X i + C Z from Dose.bending ..]
   rw [show MvPolynomial.map PowerSeries.C q * (J _*_)= C Z*(extended q * L)+ extended q * X i * L from by change extended q * (L*(X i+C Z)) = _;ring,map_add,C_mul',map_smul]; simp only [smul_eq_mul,extended]; rw [mul_comm _ Z]
lemma expose(p:Pol G)(w:Orb.Coords G N): Full.column d h x p w=Bare.field h x w ((inkD G d h).heat p):=by
 rw [column,splashed, show extended (1:Pol G)=1 from map_one _,one_mul,Dose.reflow,Dose.mapped_heat]
 generalize (inkD G d h).heat p=Q
 induction Q using MvPolynomial.induction_on with
 | C c => rw [map_C, field_C,aeval_C];rfl
 | add q r hq hr=> simp only [field_add,map_add,hq,hr]
 | mul_X q i hq=> rw [map_mul (MvPolynomial.map _),map_mul,hq,map_X,aeval_X,field_mul,field_X]
def dream (h:ℝ)(p:Pol G) := ((unmarked G h).neg.mapped Complex.ofRealHom).heat p
lemma inventory(p: Pol G)(hp:Full.within p d) (w: Orb.Coords G N): Full.column d h x p w=Bare.field h x w (dream h p):=by
 rw [dream, expose]; apply congrArg
 let f:=fun i:CosKey G d=>i.val
 obtain ⟨P,hP⟩:= exists_rename_eq_of_vars_subset_range p f Subtype.val_injective (fun i hi => ⟨⟨i,hp _ hi⟩,rfl⟩)
 let L:CosKey G d→Stem (Key G) ℂ:= Dose.arrow f
 rw [← hP, Dose.migrate,Dose.migrate]; apply congrArg _
 have he : (inkD G d h).pull L=((unmarked G h).neg.mapped Complex.ofRealHom).pull L:=Dose.strict _ _ (fun i j=>by unfold L; rw [Dose.reach,Dose.reach]; unfold inkD unmarked Dose.neg Dose.mapped Dose.pull; simp only [f,i.property,j.property,and_self, ↓reduceIte,Complex.ofRealHom_eq_coe, Complex.ofReal_neg]; rw [nightfall])
 rw [he]
end YM.SchemeRG11.Atoll
