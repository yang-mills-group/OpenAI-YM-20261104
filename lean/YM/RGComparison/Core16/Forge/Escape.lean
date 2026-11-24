import YM.RGComparison.Core16.Forge.Riot

/-!
# Entropic replacement price of ball into shells

After all tags coupled locally, BEFORE Taylor. Uniform all strongly-measurable integrations on
true probability prior.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ENNReal
variable {G:Gauge} {S : Side} {ι k T : Type} [Fintype ι] [Fintype k] [Fintype T]
variable {X:Prices} {B:Base G S ι k T}{g D : ℝ} (H:B.Admits X g)

abbrev burn (G:Gauge):= Module.finrank ℝ G.Mat
def shells (G:Gauge)(ι:Type)(r:ℝ) : Set (Sky G ι):= Set.pi Set.univ (fun _=> G.shell r)
lemma shells_ge (r:ℝ)(hr:0<r)(hm:r≤1): ((r/4)^ (burn G)) ^ Fintype.card ι ≤ (skillet G ι).real (shells G ι r):=by
   unfold skillet shells Measure.real
   rw [Measure.pi_pi]; simp only [prod_const, card_univ, ENNReal.toReal_pow]; exact pow_le_pow_left₀ (by positivity) (G.shell_ge r hr hm) _

omit [Fintype ι] in
private lemma minor {ν : Measure (Sky G ι)} [IsProbabilityMeasure ν] {V F : Sky G ι → ℝ} {J : Set (Sky G ι)}(hJ:MeasurableSet J){z:ℝ}(hz : 0 ≤ z)
   (hF:Integrable F ν) (hV:Integrable V ν) (h:∀x y,y∈J → F x ≤ z*V y)(hP:∀ x, 0 ≤ V x):
   ν.real J * (∫ x,F x ∂ν) ≤ z* ∫ x,V x ∂ν := by
   calc
     _ = ∫ _y in J, (∫ x,F x ∂ν) ∂ν:= by rw [setIntegral_const, smul_eq_mul]
     _ ≤ ∫ y in J, z*V y ∂ν:= by
         refine setIntegral_mono_on (integrable_const _|>.integrableOn) ((hV.const_mul z).integrableOn) hJ (fun y hy=>?_)
         exact (integral_mono hF (integrable_const (z*V y)) (fun x=> h x y hy)).trans_eq (by simp)
     _ ≤ ∫ y,z*V y ∂ν:= setIntegral_le_integral (hV.const_mul z) (Eventually.of_forall (fun x=> mul_nonneg hz (hP x)))
     _ = _:= integral_const_mul ..

abbrev old (u:Finset ι):= {i : ι// i∉u}

lemma migrate (U:Finset ι){z:ℝ}(hz:0≤z) {W : Set (Sky G ι)}(hW:MeasurableSet W){V : Sky G ι→ℝ}(hV:Envelope V)
   (hA:∀x,0≤ V x)(hg:0<g)(hm:g≤1)
   (h:∀ x∈W, ∀ y:Sky G ι, (∀ i∉U,x i=y i) → (∀ i∈U,nib y i≤g^2) → V x≤ z*V y):
   ((g/4)^(burn G))^U.card * (∫ x in W, V x ∂skillet G ι) ≤ z*(∫ x,V x ∂skillet G ι) := by
   let p (i:ι) := i∈U; let μ:= skillet G (old U); let ν:= skillet G ↥U
   let T := MeasurableEquiv.piEquivPiSubtypeProd (fun _:ι=>G.El) p
   let J:=shells G ↥U g
   have hJ:MeasurableSet J:=MeasurableSet.univ_pi (fun _=>G.shell_meas g)
   let F:=W.indicator V
   have hE:Envelope F:=by
       have hx (x:Sky G ι): ‖F x‖ ≤ ‖V x‖ := norm_indicator_le_norm_self ..
       exact ⟨hV.meas.indicator hW, hV.cost.choose,fun x=> (hx x).trans (hV.cost.choose_spec x)⟩
   have hs (x:Sky G ι):0≤F x:= Set.indicator_nonneg (fun _ _=>hA _ ) _
   have hx : MeasurePreserving T.symm (ν.prod μ) (skillet G ι) := by
      unfold ν μ skillet
      convert! (measurePreserving_piEquivPiSubtypeProd (fun _:ι=> G.probHaar) p).symm (T)
   have he (Q : Sky G ι→ℝ)(hQ:Envelope Q): Integrable (fun x : Sky G ↥U × Sky G (old U)=> Q (T.symm x)) (ν.prod μ) := hx.integrable_comp_of_integrable (hQ.integrable _)
   have hj (Q : Sky G ι→ℝ)(hQ:Envelope Q): (∫ x,Q x ∂skillet G ι)= ∫ b,(∫ a,Q (T.symm (a,b)) ∂ν)∂μ := (hx.integral_comp' Q).symm.trans (integral_prod_symm _ (he _ hQ))
   rw [← integral_indicator hW, hj _ hE, hj _ hV, ←integral_const_mul,← integral_const_mul]; apply integral_mono ((he _ hE).integral_prod_right.const_mul _) ((he _ hV).integral_prod_right.const_mul _); intro b
   let f (a:Sky G ↥U) := T.symm (a,b)
   have H' (Q : Sky G ι→ℝ)(hQ:Envelope Q):Integrable (Q ∘ f) ν:=
       (show Envelope (Q ∘ f) from ⟨hQ.meas.comp (T.symm.measurable.comp (measurable_id.prodMk measurable_const)),hQ.cost.choose,fun i=>hQ.cost.choose_spec (f i)⟩).integrable _
   have hr := (show ((g/4) ^ burn G)^Fintype.card ↥U ≤ ν.real J from shells_ge g hg hm)
   rw [Fintype.card_coe] at hr; refine le_trans (mul_le_mul_of_nonneg_right hr (integral_nonneg (fun i=> hs (f i)))) ?_
   refine minor hJ hz (H' F hE) (H' V hV) (fun a w hw => ?_) (fun i=>hA (f i))
   change W.indicator V (f a) ≤ _; by_cases hk:f a∈W
   · rw [Set.indicator_of_mem hk]; refine h _ hk _ (fun i hi=>?_) (fun i hi=>?_)
     · change (Equiv.piEquivPiSubtypeProd p _).symm _ _=(Equiv.piEquivPiSubtypeProd p _).symm _ i
       simp only [Equiv.piEquivPiSubtypeProd_symm_apply,dif_neg (show ¬ p i from hi)]
     have hp:= hw (⟨i,hi⟩:↥U) (Set.mem_univ _); change G.chord (f w i)^2 ≤ g^2; rw [show f w i=w ⟨i,hi⟩ from ?_]
     · exact pow_le_pow_left₀ (G.chord_nonneg _) hp _
     change (Equiv.piEquivPiSubtypeProd p _).symm _ _=_
     rw [Equiv.piEquivPiSubtypeProd_symm_apply,dif_pos (show p i from hi)]
   rw [Set.indicator_of_notMem hk]; exact mul_nonneg hz (hA _)

def riot (loc:ι→Site S)(z:Site S) (X:Prices)(r:ℝ)(R:ℕ): Set (Sky G ι):= {x | threat loc z x (R+X.b+X.b) ≤ (1+incline X)* threat loc z x R ∧ r ≤ threat loc z x R}
lemma measurableR (loc:ι→ Site S)(R:ℕ)(z : Site S)(r:ℝ) : MeasurableSet (riot (G:=G) loc z X r R):=by
   have h (R:ℕ) : Continuous fun x : Sky G ι=> threat loc z x R:= by unfold threat nib; fun_prop
   apply IsClosed.measurableSet; exact (isClosed_le (h _) (continuous_const.mul (h _))).inter (isClosed_le continuous_const (h _))

namespace Base
include H
lemma riot_cost {R:ℕ}{z:Site S}(r:ℝ)(hg:0<g)(hm:g≤1) :
   ((g/4)^(burn G)) ^ (neighborsOf B.loc R z).card * (∫ x in riot B.loc z X r R,B.output g x ∂skillet G ι) ≤
       Real.exp (rider X*weights X (R+X.b) - r /(2*dam X*g^2)) * ∫ x,B.output g x ∂skillet G ι:=by
   have hG :=@dam_pos X
   refine migrate (neighborsOf B.loc R z) (Real.exp_pos _).le (measurableR ..) (output_env H) (fun x=> output_pos H x|>.le) hg hm ?_
   intro x hx y hy hh
   refine (pair_stamp H hg hh hy hx.1).trans ?_; gcongr; exact output_pos H y|>.le; exact hx.2
end Base
end YM.RGComparison.Core16.Forge
