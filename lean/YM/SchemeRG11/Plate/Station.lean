import YM.SchemeRG11.Plate.Width
import YM.SchemeRG11.Cover.Heat
/-! Open polynomial stencils. Establish existence and exact real lifts before moments. -/
set_option autoImplicit false
set_option maxRecDepth 3500
noncomputable section
namespace YM.SchemeRG11.Tree
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial
open scoped Classical ContDiff
variable {U V E M L:Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup M] [Module ℝ M] {G:Gauge}
section general
local notation "Input" => U→ℝ
def Pulse(L: (U→ℝ) → ℝ): Prop := ∃ P:Stem U ℝ,∀ z:U→ℝ,L z=sense z P
lemma Pulse.smul (c:ℝ){L: (U→ℝ) → ℝ} (h:Pulse L): Pulse (fun z => c*L z):=by obtain ⟨P,H⟩:=h; exact ⟨c • P,fun z=>by dsimp only; rw [H,map_smul];rfl⟩
lemma Pulse.add {L J:(U→ℝ) → ℝ} (h:Pulse L) (j:Pulse J): Pulse (fun z => L z+J z):=by obtain ⟨P,H⟩:=h; obtain ⟨Q,K⟩:=j; exact ⟨P+Q,fun z=>by dsimp only; rw [H,K,map_add]⟩
lemma zeroP : Pulse (fun _:U→ℝ=>(0:ℝ)):=⟨0,fun _=> (map_zero _).symm⟩
lemma sumP {s:Finset V}(f:V→ (U→ℝ)→ℝ)(h:∀ i∈s,Pulse (f i)): Pulse (fun z=> ∑ i∈s,f i z):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; apply zeroP
 | insert a s ha ih=> simp_rw [Finset.sum_insert ha]; exact (h _ (Finset.mem_insert_self ..)).add (ih (fun i hi=> h _ (Finset.mem_insert_of_mem hi)))

def Nimbus(f: (U→ℝ) → ℝ) : Prop := ∃ P:Paper U ℝ,∀ z:U→ℝ,f z=MvPolynomial.aeval z P
lemma Nimbus.smul (c:ℝ){L:(U→ℝ) → ℝ} (h:Nimbus L): Nimbus (fun z => c*L z):=by obtain ⟨P,H⟩:=h; exact ⟨c • P,fun z=>by dsimp only; rw [H,map_smul];rfl⟩
lemma Nimbus.add {L J:(U→ℝ) → ℝ} (h:Nimbus L) (j:Nimbus J): Nimbus (fun z => L z+J z):=by obtain ⟨P,H⟩:=h; obtain ⟨Q,K⟩:=j; exact ⟨P+Q,fun z =>by dsimp only; rw [H,K,map_add]⟩
lemma Nimbus.mul {L J:(U→ℝ) → ℝ} (h:Nimbus L) (j:Nimbus J): Nimbus (fun z=> L z*J z):=by obtain ⟨P,H⟩:=h; obtain ⟨Q,K⟩:=j; exact ⟨P*Q,fun z =>by dsimp only; rw [H,K,map_mul]⟩
lemma Pulse.evolves {L:(U→ℝ) → ℝ} (h:Pulse L): Nimbus L:=by obtain ⟨P,H⟩:=h; exact ⟨leaf P,fun z=>by rw [H,Haze.realTaste]⟩
lemma sumN {s:Finset V}(f:V→ (U→ℝ)→ℝ)(h:∀ i∈s,Nimbus (f i)): Nimbus (fun z=> ∑ i∈s,f i z):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact zeroP.evolves
 | insert a s ha ih=> simp_rw [Finset.sum_insert ha]; exact (h _ (Finset.mem_insert_self ..)).add (ih (fun i hi=> h _ (Finset.mem_insert_of_mem hi)))

def Kokon (t:Bool) (L:(U→ℝ)→ℝ):Prop:=if t then Nimbus L else Pulse L
lemma Kokon.add {t} {f g:(U→ℝ)→ℝ}(hf:Kokon t f)(hg:Kokon t g):Kokon t (fun z=> f z+g z):=by
 cases t; · exact Pulse.add hf hg
 exact Nimbus.add hf hg
lemma Kokon.smul {t}{f:(U→ℝ)→ℝ}(hf:Kokon t f)(c:ℝ): Kokon t (fun z=> c*f z):=by
 cases t; · exact Pulse.smul c hf
 exact Nimbus.smul c hf
lemma sumK {s:Finset V}(f:V→ (U→ℝ)→ℝ){t}(h:∀ i∈s,Kokon t (f i)): Kokon t (fun z=> ∑ i∈s,f i z):=by
 cases t; · exact sumP f h
 exact sumN f h

def Loft (f:(U→ℝ)→E)(t:Bool): Prop:= ∀ Q:E→ₗ[ℝ] ℝ,Kokon t (fun z=>Q (f z))
lemma Loft.treat {t : Bool}{f:(U→ℝ)→E}(hf:Loft f t)(L:E→ₗ[ℝ] M): Loft (fun z=>L (f z)) t:=fun Q=> hf (Q.comp L)
lemma Loft.add {t}{f g:(U→ℝ)→E}(hf:Loft f t)(hg:Loft g t): Loft (fun z=>f z+g z) t:=fun Q=>by simpa only [map_add] using! Kokon.add (hf Q) (hg Q)
lemma Loft.smul {t:Bool}{f:(U→ℝ)→E}(hf:Loft f t)(c:ℝ):Loft (fun z=> c • f z) t:=fun Q=> by simpa only [map_smul] using! (hf Q).smul c
lemma sky {t:Bool}(f:V→(U→ℝ)→E)(s:Finset V)(h:∀ i∈s,Loft (f i) t):Loft (fun z=>∑ i∈s,f i z) t:=fun Q=>by simp_rw [_root_.map_sum]; exact sumK _ (fun i hi=> h _ hi _)
lemma sky_zero (t:Bool):Loft (fun _:U→ℝ=>(0:E)) t:=fun Q=>by
 simp_rw [map_zero]; cases t
 · exact zeroP
 exact Pulse.evolves zeroP
variable {J : Type*} [AddCommGroup J] [Module ℝ J]
lemma Loft.both {f:(U→ℝ)→E}{g:(U→ℝ)→M}[FiniteDimensional ℝ E][FiniteDimensional ℝ M]
 (hf:Loft f false)(hg:Loft g false)(L:E→ₗ[ℝ] M→ₗ[ℝ] J): Loft (fun z=> L (f z) (g z)) true:=by
 intro Q; let R:=Module.finBasis ℝ E; let S:=Module.finBasis ℝ M
 change Nimbus (fun z=>Q (L (f z) (g z)))
 have he (z):Q (L (f z) (g z))=∑ i,∑ j,(R.repr (f z)) i*((S.repr (g z)) j*Q (L (R i) (S j))):=by
   conv_lhs=> rw [← R.sum_repr (f z),← S.sum_repr (g z)]
   simp only [map_sum, map_smul,smul_eq_mul]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul, smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
 simp_rw [he]; apply sumN; intro i _; apply sumN; intro j _
 apply (Pulse.evolves (L:=fun z=>R.coord i (f z)) (hf _)).mul
 have hx: Nimbus (fun z=> Q (L (R i) (S j))* ((S.repr (g z)) j)):= (Pulse.evolves (L:=fun z=>S.coord j (g z)) (hg _)).smul _; simp_rw [mul_comm (Q _)] at hx; exact hx
end general
abbrev Code (G:Gauge)(L:Type*):=Edge (Four L) × G.ColorIndex
def cant (A: trunk G L): Code G L→ℝ:=fun i=> A i.1 i.2
def tint(z:Code G L→ℝ): trunk G L:=fun l=> WithLp.toLp 2 (fun i=>z (l,i))
lemma tint_inv(A:trunk G L):tint (cant A)=A:=by funext e; rfl
lemma cant_inv(z: Code G L→ℝ):cant (tint z)=z:=rfl
variable [AddCommGroup L] [One L]
omit [AddCommGroup L] [One L] in
lemma slice(e:Edge (Four L)) :Loft (fun z:Code G L→ℝ => tint z e) false:=by
 intro Q;change Pulse _; let R:=EuclideanSpace.basisFun G.ColorIndex ℝ
 have he(z:Code G L→ℝ):Q (tint z e)=∑ i,z (e,i)*Q (R i):=by rw [← R.sum_repr (tint z e),map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul]; simp [R,tint]
 simp_rw [he,mul_comm _ (Q _)]; apply sumP; intro i _; apply Pulse.smul; exact ⟨Finsupp.single (e,i) 1,fun _=>by rw [sense,Finsupp.linearCombination_single,one_smul]⟩
lemma heelLoft {A: (U→ℝ)→trunk G L} (hA:∀ e, Loft (fun z => A z e) false) (x:Four L)(d:Step): Loft (fun z=>heel d x (A z)) false:=by
 unfold heel; split
 · simpa only [neg_one_smul] using (hA _).smul (-1)
 exact hA _
lemma walksLoft{A: (U→ℝ)→trunk G L} (hA:∀ e, Loft (fun z => A z e) false) (x:Four L)(w:Walk): Loft (fun z=> mileage x w (A z)) false:=by
 induction w generalizing x with
 | nil=> exact sky_zero false
 | cons d w ih=> simp_rw [mileage]; exact Loft.add (heelLoft hA _ _) (ih _)
lemma walksLoft₂{A: (U→ℝ)→trunk G L}(hA:∀ e, Loft (fun z => A z e) false)(x:Four L)(w:Walk): Loft (fun z=> cohort x w (A z) (A z)) true:=by
 induction w generalizing x with
 | nil=> exact sky_zero true
 | cons d w ih=> simp_rw [cohort]; exact Loft.add (ih _) (Loft.both (heelLoft hA x d) (walksLoft hA _ _) G.ad)
lemma loft_pi {J:Type*}[Fintype J]{t:Bool}(A: (U→ℝ)→ J→E)(H:∀ i,Loft (fun z=> A z i) t):Loft A t:=by
 have he z:A z=∑ i:J,Pi.single i (A z i):=by ext i; simp
 change Loft A t
 let p(i:J): E→ₗ[ℝ] (J→E):=LinearMap.single ℝ (fun _:J=> E) i
 let f(i:J):=fun z=>p i (A z i)
 rw [show A=_ from funext (g:=fun z=>∑ i:J,f i z) he]
 exact sky _ _ fun i _=> Loft.treat (H i) (p i)
lemma lofty {A:(U→ℝ)→ trunk G L}(ha:∀ i, Loft (fun z=> A z i) false)(x:Four L)(j:ℕ)(t:Bool): Loft (fun z=>part t x j (A z) (A z)) t:=by
 refine loft_pi _ fun i=> loft_pi _ fun k=>loft_pi _ fun r=>?_
 unfold part; refine (sky _ _ (fun s _=> Loft.smul ?_ _)).smul _
 cases t; · exact walksLoft ha _ _
 exact walksLoft₂ ha _ _
lemma styleLoft {A:(U→ℝ)→trunk G L}(ha:∀ i,Loft (fun z=> A z i) false)(x:Four L)(j:ℕ)(t:Bool)(q:ℝ)(s:Signed): Loft (fun z=>style t q x j s (A z) (A z)) t:=by
 let W z:=wideLink G s (A z)
 have hp (i:Edge (Four L)): Loft (fun z=> W z i) false:=by unfold W; simp_rw [Bare.wideLink_apply]; apply Loft.smul; apply ha
 exact (((lofty hp (affine s⁻¹ 0 x) j t).treat radialMap).smul (q^(-(j+2:ℤ)))).treat (Taylor.turn s.ortho)
lemma sum_token(t:Bool)(c:ℝ)(s:Finset V)(f:V→(U→ℝ)→E) (H:∀ v,Loft (f v) t): Loft (fun z=> c • ∑ i∈s,f i z) t:= Loft.smul (sky _ _ (fun i _=> H i)) c
set_option maxRecDepth 15000 in
lemma starLoft (x:Four L)(j:ℕ)(t:Bool)(q:ℝ):Loft (fun z:Code G L→ℝ=> starJet t q x j (tint z) (tint z)) t:= by
 let f (i : Signed)(z:Code G L→ℝ):= style t q x j i (tint z) (tint z)
 have he(i:Signed):Loft (f i) t:=styleLoft (A:=tint) slice x j t q i
 let Y (z:Code G L→ℝ):=((Fintype.card Signed:ℝ)⁻¹ • ∑ i:Signed,f i z)
 have hy: Loft Y t:= sum_token  t ((Fintype.card Signed:ℝ)⁻¹) Finset.univ f he
 exact hy

end YM.SchemeRG11.Tree
