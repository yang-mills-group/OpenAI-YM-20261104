import YM.RG06.Wilson.Site
import YM.PertExtension.TopCalibration
/-!
# Finite rank r rooted potential tensors, expanded Feynman rules
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.RG06.Tokens
open Function Filter Lattice RG Labels Source Bid
open MvPolynomial hiding C X
open scoped Matrix.Norms.Frobenius BigOperators Topology InnerProductSpace Classical ContDiff
variable {G : Gauge}{X: Type}{d : ℕ}{F: Labels.Frame G d}{T: Finset Cover}

local notation "K" => Kernel G ℤ
variable (S : SectionData F)
local notation "Index" => Source.Index G

def pierce (z:Index T) : PowerSeries K := if z.2.2.2 then PowerSeries.map varnish (emitSeries G z.1.val z.2.1 z.2.2.1) else emitSeries G z.1.val z.2.1 z.2.2.1

def native : ℂ→+*PowerSeries K := PowerSeries.C.comp MvPolynomial.C
/-- All diagrams before measure. Positions spatially on infinite cover, native
 link difference with no period tail. Complex coefficients for real stencils. -/
def interior {T:Finset Cover}(p : Formula G T) := MvPolynomial.eval₂Hom native pierce p

lemma piercing (z:Index T)(i)(v:Links ℤ G.Color):applyHere v (PowerSeries.coeff i (pierce z))= Rules.entryCoeff v z i:=by
  unfold pierce; split
  · next h => rw [PowerSeries.coeff_map,siteStar,emit_here]; unfold Rules.entryCoeff Rules.entryMap; rw [if_pos h]; rfl
  next h=> rw [emit_here]; unfold Rules.entryCoeff Rules.entryMap; rw [if_neg h]; rfl

lemma entryLogo (P: Formula G T)(v:Links ℤ G.Color):PowerSeries.map (applyHere v).toRingHom (interior P)=Rules.formulaRule v P:=by
  have h(z:Index T):PowerSeries.map (applyHere v).toRingHom (pierce z)= PowerSeries.mk (Rules.entryCoeff v z) := by
    ext1 e; rw [PowerSeries.coeff_map,PowerSeries.coeff_mk]; exact piercing z e v
  induction P using MvPolynomial.induction_on with
  | C c=> simp [interior,Rules.formulaRule,native]
  | add p q hp hq=> convert congr_arg₂ (· + ·) hp hq using 1 <;> simp [interior,Rules.formulaRule]
  | mul_X p i hp=> simp only [interior,_root_.map_mul,MvPolynomial.eval₂Hom_X',h,Rules.formulaRule]; rw [show PowerSeries.map (applyHere v).toRingHom (eval₂Hom native pierce p)= _ from hp]; rfl

lemma native_ranked (P: Formula G T) (e) : ranked (PowerSeries.coeff e (interior P)) e:=by
  have h (i)(z:Index T): ranked (PowerSeries.coeff i (pierce z)) i:=by
    unfold pierce; split <;> first | rw [PowerSeries.coeff_map]; exact varnish_ranked i (emit_ranked ..) | exact emit_ranked ..
  induction P using MvPolynomial.induction_on generalizing e with
  | C c=>
    simp only [interior,native,MvPolynomial.eval₂Hom_C,RingHom.coe_comp,Function.comp_apply,PowerSeries.coeff_C]; split
    · next he=> subst e; exact isWeightedHomogeneous_C ..
    · exact isWeightedHomogeneous_zero ..
  | add p q hp hq=>unfold interior; rw [_root_.map_add,_root_.map_add]; exact (hp e).add (hq e)
  | mul_X p i hp=>unfold interior; rw [_root_.map_mul,MvPolynomial.eval₂Hom_X',PowerSeries.coeff_mul]; apply IsWeightedHomogeneous.sum; intro v hh; rw [← Finset.mem_antidiagonal.mp hh]; exact (hp v.1).mul (h v.2 _)

def casing (c:F.Coeff)(e:ℕ) : K:=PowerSeries.coeff e (interior (S.evalC c))
lemma wrapRule (A:Links ℤ G.Color)(c:F.Coeff)(e):applyHere A (casing S c e) = CubicMatch.term e (fun g=> S.evaluate c (Rules.expRay A g)) := by
  rw [(Rules.section_exact S A c).get]
  exact (PowerSeries.coeff_map (applyHere A).toRingHom e _).symm.trans (congr_arg _ (entryLogo (S.evalC c) A))
lemma inside (A:Links ℤ G.Color)(c:F.Coeff):Rules.HasCoefficients (fun g=> S.evaluate c (Rules.expRay A g)) (fun e=>applyHere A (casing S c e)) := ⟨(Rules.section_exact S A c).regular,fun e=> (wrapRule S A c e).symm⟩
lemma bundled_add (c b:F.Coeff)(e):casing S (c+b) e=casing S c e+casing S b e:=by unfold casing interior; rw [map_add,_root_.map_add,_root_.map_add]
lemma bundled_smul (c:F.Coeff)(z:ℂ)(e):casing S (z • c) e= z • casing S c e:=by
  unfold casing interior
  rw [map_smul,Algebra.smul_def,MvPolynomial.algebraMap_eq,_root_.map_mul,MvPolynomial.eval₂Hom_C,native,RingHom.comp_apply,PowerSeries.coeff_C_mul,Algebra.smul_def,MvPolynomial.algebraMap_eq]

lemma doesNotStart (h: Bid.pop S)(i:F.Index)(e:ℕ)(he:e<(F.grades i).2) : casing S (Pi.single i 1) e = 0 :=by
  apply unisolvent; intro A
  rw [wrapRule,map_zero,(Rules.section_exact S A _).get,Rules.scaled_exact S h i A,PowerSeries.coeff_mul_X_pow',if_neg (not_le_of_gt he)] -- name

def stencil (i : F.Index)(e:ℕ) := casing S (Pi.single i 1) (e+(F.grades i).2)
abbrev charge (i:F.Index)(e:ℕ) := e+(F.grades i).2
lemma insertion_charge (i:F.Index)(e:ℕ): ranked (stencil S i e) (charge i e):= native_ranked _ _
theorem replaces (h:Bid.pop S)(A:Links ℤ G.Color)(i:F.Index): Rules.HasSeries
    (fun g=> S.evaluate (Pi.single i 1) (Rules.expRay A g)) ((PowerSeries.mk (fun e=> applyHere A (stencil S i e))) * (PowerSeries.X ^ (F.grades i).2)):=by
  have he : PowerSeries.mk (fun e=> applyHere A (stencil S i e))=Rules.scaledRule S A i:=by
    ext1 e;rw [PowerSeries.coeff_mk,stencil,wrapRule,(Rules.section_exact S A _).get];simp [Rules.scaledRule]
  rw [he,← Rules.scaled_exact S h]; exact Rules.section_exact S A _
lemma first_evaluation (e:ℕ)(A:Links ℤ G.Color)(i:F.Index) :
    applyHere A (stencil S i e)=PowerSeries.coeff e (Rules.scaledRule S A i):=by
 rw [stencil,wrapRule,(Rules.section_exact S A _).get,Rules.scaledRule,PowerSeries.coeff_mk]

/-! Leading slot polynomials expressed by linear curls ON THE LATTICE, not via matching to Maxwell on-shell yet. Repeated/multiple reads agree on this same one-form kernel. -/

def linearStep [AddCommGroup X][One X](s:Lattice.Step)(o:Four X)(i:G.ColorIndex):Kernel G X:= if s.neg then - MvPolynomial.X (s.used o,i) else MvPolynomial.X (s.used o,i)
lemma linear_read [AddCommGroup X][One X](A:Links X G.Color)(s:Lattice.Step)(o:Four X) (i:G.ColorIndex):applyHere A (linearStep s o i)= (↑(Rules.signed s o A i):ℂ) := by
  unfold Rules.signed linearStep; split
  · rw [map_neg,finger_X]; unfold finger;rw [show (-A (s.used o)) i= -(A (s.used o) i) from rfl]; simp
  exact finger_X ..

def linearWalk [AddCommGroup X][One X](o:Four X)(i:G.ColorIndex):Walk→Kernel G X
  | []=>0
  | a::l=>linearStep a o i+linearWalk (o+a.vec) i l
lemma linear_exact [AddCommGroup X][One X](A:Links X G.Color)(o:Four X)(i:G.ColorIndex)(w:Walk) : applyHere A (linearWalk o i w)= (↑(Rules.linPath A o w i):ℂ) := by
 induction w generalizing o with
 | nil=>unfold linearWalk Rules.linPath;rw [map_zero]; simp -- withLp
 | cons s w ih=>rw [linearWalk,Rules.linPath,_root_.map_add,linear_read,ih];exact (Complex.ofReal_add ..).symm
lemma walk_charge [AddCommGroup X][One X](o:Four X)(i:G.ColorIndex)(w:Walk) : ranked (linearWalk o i w) 1:=by
  induction w generalizing o with
  | nil=>exact isWeightedHomogeneous_zero ℂ oneRank _
  | cons s w ih=>
    unfold linearWalk; apply IsWeightedHomogeneous.add _ (ih _); unfold linearStep; split
    · apply @Submodule.neg_mem _ _ _ _ _ (weightedHomogeneousSubmodule ℂ oneRank 1); exact node_X _
    exact node_X _

def curls (p:RG.Slot × G.ColorIndex) : K:= linearWalk p.1.offset p.2 (square p.1.plaq.val.1 p.1.plaq.val.2)
lemma curls_here (p:RG.Slot × G.ColorIndex)(A:Links ℤ G.Color):applyHere A (curls p)= ( (Rules.linPath A p.1.offset (square p.1.plaq.val.1 p.1.plaq.val.2) p.2:ℝ):ℂ):= linear_exact ..
def remit: MvPolynomial (RG.Slot × G.ColorIndex) ℂ →ₐ[ℂ] K:= aeval curls
lemma remitted_scale {r:ℕ}{p:MvPolynomial (RG.Slot × G.ColorIndex) ℂ}(h:ranked p r): ranked (remit p) r:=
    Symbols.graded_substitution _ _ _ (fun i=>by rw [remit,aeval_X]; exact walk_charge ..) h

open PertExtension.Heat.Top
private theorem establishes (i:F.Index){m:ℕ}(B:Fin m→RG.Slot)(P:Pose G m)(hp:lows P (F.grades i).2)(hs:S.evaluate (Pi.single i 1)=lumin P ∘ mapped B):
    stencil S i 0=remit (rawPart B P (F.grades i).2):=by
  refine unisolvent _ _ fun v=>?_
  let f:ℕ:= (F.grades i).2
  rw [stencil,Nat.zero_add,wrapRule,hs]
  change CubicMatch.term f (fun t:ℝ=>lumin P (mapped B (Rules.expRay v t)))=_
  rw [Rules.pose_leading B P f hp]
  let Q : Pose G m:= weightedHomogeneousComponent oneRank f P
  have he: applyHere v (remit (rename (fun z:Fin m×G.ColorIndex=>(B z.1,z.2)) Q))= aeval (fun z:Fin m × G.ColorIndex => applyHere v (curls (B z.1,z.2))) Q:=by
    have hv : (applyHere v).comp (remit.comp (rename (fun z:Fin m × G.ColorIndex=>(B z.1,z.2))))= aeval (fun z:Fin m × G.ColorIndex => applyHere v (curls (B z.1,z.2))) := by
      ext j; simp [remit]
    exact DFunLike.congr_fun hv Q
  rw [show rawPart B P (F.grades i).2=rename (fun z:Fin m×G.ColorIndex=>(B z.1,z.2)) Q from rfl, he]
  simp_rw [curls_here,aeval_eq_eval₂Hom,coe_eval₂Hom,eval₂_eq]
  unfold Q; rw [support_weightedHomogeneousComponent]
  simp only [coeff_weightedHomogeneousComponent,Finsupp.weight_apply, Rules.count, oneRank, smul_eq_mul,mul_one, Algebra.algebraMap_self,RingHom.id_apply]
  apply Finset.sum_congr rfl fun b hb=>?_
  have hv:f=(Finsupp.sum b fun _ t=>t):=(Finset.mem_filter.mp hb).2.symm
  rw [if_pos hv.symm]
  rfl

theorem actual_on_legs (D:Data F)(h:Valid D S) (i:F.Index):stencil S i 0=remit (rawPart (D.columns i) (D.shape i) (F.grades i).2):=establishes S _ _ _ (D.low i) (h i)

-- Any pure-gradient perturbation in ANY of the lattice-potential variables annihilates these terms
-- (not the claim for positive coupling order!)
def latticeGradient [AddCommGroup X][One X](w:Four X→G.Color):Links X G.Color:= fun e=>w e.1 - w (e.1+step e.2)
lemma curls_gradient (u:RG.Slot × G.ColorIndex)(A:Links ℤ G.Color)(w:Cover→G.Color):applyHere (A+latticeGradient w) (curls u)=applyHere A (curls u):=by
  simp only [curls_here,Rules.square_lead]
  apply congr_arg (fun p:G.Color=> ((p u.2:ℝ):ℂ))

  simp only [Pi.add_apply,latticeGradient,add_right_comm (_:Cover) (step u.1.plaq.val.1) (step u.1.plaq.val.2)]
  abel
lemma horizontal (h: Bid.pop S)(p:F.Index)(A:Links ℤ G.Color)(w:Cover→G.Color):
    applyHere (A+latticeGradient w) (stencil S p 0) = applyHere A (stencil S p 0):=by
  obtain ⟨b,B,_,P,hS,hP⟩:=h p
  rw [establishes S p B P hP hS]
  have hv : (applyHere (A+latticeGradient w)).comp remit=(applyHere A).comp remit := by ext i; simpa [remit] using! curls_gradient i A w
  exact DFunLike.congr_fun hv _
end YM.RG06.Tokens
