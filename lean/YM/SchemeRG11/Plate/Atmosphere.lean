import YM.SchemeRG11.Plate.Cost
import YM.SchemeRG11.Cover.Cloud
import YM.SchemeRG11.Cover.Bloom
import YM.SchemeRG11.Wilson.Cover
/-! Open propagation bridge, same scalar Fourier & auxiliary normal choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Atoll
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology BigOperators
variable {G : Gauge} {N : Side}

abbrev Shaft (G:Gauge) := Tree.Code G ℤ
def land (G:Gauge) : Dose (Shaft G) ℝ where
 pulse p q:=if p.2=q.2 ∧ p.1.2 = q.1.2 then coverLine (p.1.1-q.1.1) else 0
 beats p q:=by split
               next h=> rw [if_pos ⟨h.1.symm,h.2.symm⟩,← neg_sub q.1.1,nod]
               next h=> rw [if_neg (fun w=> h ⟨w.1.symm,w.2.symm⟩)]
abbrev Pill (G:Gauge)(N:Side):=Tree.Code G (Per N)
def holds(p:Pill G N):= Orb.formElem p.1 (Maxwell.unitColor G p.2)
def spray (G:Gauge)(N:Side):Dose (Pill G N) ℝ where
 pulse p q:= Orb.covar (holds p) (holds q)
 beats p q:=by simp only [Orb.covar_formula]; apply Orb.form_symm
lemma spray_eq (p q:Pill G N): (spray G N).pulse p q=if p.2=q.2 ∧ p.1.2=q.1.2 then thread (q.1.1-p.1.1)-thread (q.1.1+p.1.1+step p.1.2) else 0:=by
 simp only [spray,holds,Orb.covar_link,Align.to_color,Maxwell.unitPaint]; split_ifs <;> simp_all

def receive (p:Pill G N): Orb.Coords G N →L[ℝ] ℂ:=Complex.ofRealCLM ∘L Warp.strike (Align.picks (holds p))
lemma record (p:Pill G N)(A:Orb.Coords G N) : receive p A=Complex.ofReal (cant (Orb.expand G N A).val p):=by simp only [receive,ContinuousLinearMap.comp_apply,Warp.strike_eq, Align.dot_expand]; unfold holds cant; change (↑(inner ℝ _ (Maxwell.unitColor G p.2)):ℂ)=_; rw [Align.to_color]
lemma payment(p q:Pill G N): ∫ x, receive p x * receive q x ∂Orb.data G N= Complex.ofReal ((spray G N).pulse p q):=by simp only [receive,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul, integral_complex_ofReal, Warp.field_quad,Align.dot_inverse];rfl
lemma flat(p:Pill G N):∫ x,receive p x ∂Orb.data G N=0:=by simp only [receive,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,integral_complex_ofReal, Warp.field_mean,Complex.ofReal_zero]
abbrev SO(G:Gauge)(N:Side):= (spray G N).mapped Complex.ofRealHom
lemma introP (p:Paper (Pill G N) ℂ):
 (∫ x, aeval (fun i=>receive i x) p ∂Orb.data G N)=(SO G N).avg p:=
 letI:= Orb.isLaw (G:=G) (n:=N); Haze.cash_products (Orb.data G N) receive flat (SO G N) payment p
open Pert.Full
abbrev Touch(G:Gauge):= Stem (Shaft G) ℝ
abbrev combo(p : Touch G)(u:E4)(c:Full.Channel G) := sense (cant (Full.material c u)) p
lemma combos(p:Touch G)(c:Full.Channel G): Continuous (fun u:E4=> combo p u c):=by
 induction p using Finsupp.induction_linear with
 | zero=> simp; exact continuous_const
 | add p q hp hq=> simp only [combo,_root_.map_add]; exact hp.add hq
 | single i b=> let F := fun u=>material c u i.1;simp only [combo,sense,Finsupp.linearCombination_single, cant,smul_eq_mul]; exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : G.ColorIndex=>ℝ) i.2).comp (Full.mat_cont c _))
def tones (p q:Touch G)(u:E4):= (delta u)⁻¹ * ∑ c : Full.Channel G,combo p u c*combo q u c
lemma tones_comm(p q:Touch G):tones p q=tones q p:=by unfold tones; simp only [mul_comm (combo p _ _)]
lemma tones_int(p q:Touch G):IntegrableOn (tones p q) Full.cube:=by
 have he:= continuous_finsetSum Finset.univ (fun (i:Full.Channel G) _=> (combos p i).mul (combos q i)); obtain ⟨C,hC⟩ := IsCompact.exists_bound_of_continuousOn cube_compact he.continuousOn; exact Full.delta_integrable.mul_bdd he.aestronglyMeasurable ((ae_restrict_mem cube_compact.measurableSet).mono hC)
lemma notes_single(p q:Shaft G):volumeFactor*(∫ u in Full.cube,tones (Finsupp.single p 1) (Finsupp.single q 1) u)= (land G).pulse p q:=by
 have H(c:Full.Channel G)(r:Shaft G)(u:E4):combo (Finsupp.single r 1) u c=Align.shoot c u r.2 r.1.1 r.1.2:=by
   rw [combo,sense,Finsupp.linearCombination_single,one_smul,cant,← Align.to_color,real_inner_comm]; apply Align.shoot_dual
 simp_rw [tones,H,Align.channel_fusion,Align.to_color,Maxwell.unitPaint]
 by_cases h:p.2=q.2∧p.1.2=q.1.2
 · simpa only [if_pos h.2.symm,if_pos h.1.symm,one_mul,Dose.bed,land,if_pos h] using! (show volumeFactor*(∫ u in _,(Full.delta u)⁻¹*Full.wave false (p.1.1-q.1.1) u)=_ from (rfl : _ = coverLine (p.1.1-q.1.1)))
 simp only [land,if_neg h]; by_cases he:p.2=q.2
 · simp only [if_neg (fun (b:q.1.2=p.1.2)=>h ⟨he,b.symm⟩),zero_mul,mul_zero,integral_zero]
 simp only [if_neg (Ne.symm he),mul_zero,zero_mul,integral_zero]
lemma tone_add (p q v:Touch G): tones (p+q) v=tones p v+tones q v:=by funext u;unfold tones combo;simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib,mul_add]
lemma tone_scale (c:ℝ)(p q:Touch G): tones (c • p) q=fun u=>c*tones p q u:=by funext u; simp only [tones,combo,map_smul,smul_eq_mul, mul_assoc, ← Finset.mul_sum]; rw [mul_left_comm]
lemma supDbl (p q:Touch G): volumeFactor * (∫ u in Full.cube,tones p q u)= (land G).bed p q:=by
 let Y(p q:Touch G):=volumeFactor*(∫ u in Full.cube, tones p q u)
 let D:= land G
 have he(p q: Shaft G): Y (Finsupp.single p 1) (Finsupp.single q 1)=D.bed (Finsupp.single p 1) (Finsupp.single q 1):=by rw [Dose.bed,sense,Finsupp.linearCombination_single,one_smul,D.single_wind]; exact notes_single ..
 have trunk(p:Touch G) (H:∀ q:Shaft G, Y p (Finsupp.single q 1)=D.bed p (Finsupp.single q 1)) (Q:Touch G): Y p Q=D.bed p Q:=by
   induction Q using Finsupp.induction_linear with
   | zero=> simp [Y,Dose.bed,tones]
   | add a b ha hb=> unfold Y; rw [tones_comm p (a+b),tone_add,tones_comm a,tones_comm b,integral_add' (tones_int ..) (tones_int ..),mul_add]; rw [show D.bed p (a+b)=D.bed p a+D.bed p b from map_add ..]; exact congrArg₂ (·+·) ha hb
   | single q b=> rw [show Finsupp.single q b = b • Finsupp.single q 1 by simp, show D.bed p (b•_)=b*D.bed p (Finsupp.single q 1) from (map_smul ..), ← H]; unfold Y; rw [tones_comm p, tone_scale, integral_const_mul, tones_comm _ p];ring
 change Y p q=_; apply trunk p _ q; intro z; rw [D.bed_comm]; unfold Y; rw [tones_comm]; apply trunk (Finsupp.single z 1) (he z) p
lemma nightfall (u v:Labels.Key G)(h:ℝ) : link h u v= (land G).bed (h^(-(u.1+2:ℤ)) • alpha (0:Cover) u.1 ((axes G _).coord u.2)) (h^(-(v.1+2:ℤ)) • alpha (0:Cover) v.1 ((axes G _).coord v.2)):=by
 let p(k:Labels.Key G):Touch G:=h^(-(k.1+2:ℤ)) • alpha (0:Cover) k.1 ((axes G _).coord k.2)
 have he (k:Labels.Key G)(t:E4)(c): combo (p k) t c =Full.leg h k c t:=by
   unfold combo p; rw [map_smul, alpha_at,← map_smul, ← coins,secular];rfl
 unfold link spectral; rw [← supDbl]; change _= volumeFactor * ∫ q in Full.cube, tones (p u) (p v) q
 simp_rw [tones,he]
end YM.SchemeRG11.Atoll
