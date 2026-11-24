import YM.OPE.Compatible.Basil.Tinct
/-!
# Rare under vertical tests when globally small W. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (M:Leaf S R)
variable (η r U Y : ℝ) {b:LogField G c}{A d Z q k z:ℝ}
lemma slipping (j:F.Free) (hh:X.seeds.place=∅) (h:Rotator P L η r U Y X) (hF:X.V=represent b)
 (hA:0≤A)(hv:‖b‖≤ d)(ht:0≤k) (hy:∀ g:F.Slice G,‖(X.wrapY g).μ j.val‖≤ Z)
 (hG : ∀ a:G.Color, ‖a‖ ≤ q → G.chord (G.lieExp a) ≤ A * ‖a‖)
 (hk : Z+gStep R.beta*((Fintype.card G.ColorIndex:ℝ)*k) ≤ q)(hd : d ≤ q)
 (hp:∀ g:F.Slice G, M.ingredient (F.drape g)≠0 → A*(Z+gStep R.beta*((Fintype.card G.ColorIndex:ℝ)*k))+A*d< G.chord (g j))
 (he: (Fintype.card G.ColorIndex:ℝ) * (2 * Real.exp (-k + payE η r U (tubularPrice G L)/2))≤ z^2) : Flick H X M p z:=by
   let t (i:G.ColorIndex) : Tubular f G:= (j.val,i)
   let J i := {q:Air f G| k ≤ |q (t i)|}; let O:= ⋃ i∈(univ:Finset G.ColorIndex),J i
   have hh': Rotator P L η r U Y X := h
   have hB i : X.dice.real (J i)≤2 * Real.exp (-k + payE η r U (tubularPrice G L)/2):=by
     have hx := Poll.rectangle (M:=payE η r U (tubularPrice G L)) h.fullC.posSemidef (fun v => (le_abs_self _).trans
       (Control.top (h.scale.mate X.shutter) h.full.prices.le v)) {t i} k 1 zero_le_one
     simp only [card_singleton, Finset.mem_singleton, forall_eq, pow_one, neg_mul,one_mul,one_pow,mul_one,Nat.cast_one] at hx; exact hx
   refine ⟨O, Finset.measurableSet_biUnion _ fun i _=>measurableSet_le measurable_const (show Continuous (fun z:Air f G=> |z (t i)|) by fun_prop).measurable,?_ ,?_⟩
   · apply (measureReal_biUnion_finset_le ..).trans; apply (Finset.sum_le_sum fun i _=> hB i).trans; rw [sum_const,nsmul_eq_mul,card_univ]; exact he
   intro g u hU
   unfold into premium at hU; split at hU; swap; · exact (hU rfl).elim
   let K:= X.wrapY g; let y:= K.liftA R.beta u
   have ht' : M.ingredient (K.input y)≠0:= left_ne_zero_of_mul (left_ne_zero_of_mul hU)
   have hD:= hp (K.view y) ht'
   rw [←F.off_tree (K.view y) j,show F.drape (K.view y) j.val= _ from K.viewing _ _ (outboard K hh _ j.property)] at hD
   by_contra hz
   have hP : ‖K.atmos u j.val‖ ≤ (Fintype.card G.ColorIndex:ℝ) * k := color_cover ht _ fun i=> (lt_of_not_ge (fun (he: k ≤ |u (t i)|)=> hz (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨mem_univ _,he⟩⟩))).le
   have hx : ‖y j.val‖≤ Z+gStep R.beta*((Fintype.card G.ColorIndex:ℝ)*k):=by
     have hp: 0≤ gStep R.beta:= by unfold gStep; positivity
     unfold y liftA; rw [Pi.add_apply,Pi.smul_apply]; apply le_trans (norm_add_le ..) (add_le_add (hy g) ?_); rw [norm_smul, Real.norm_of_nonneg hp]; gcongr
   have hv' : G.chord (replica S.ratio X.V j.val) ≤ A*d:=by
     unfold replica; split
     next => simp only [G.chord_one]; exact mul_nonneg hA ((norm_nonneg _).trans hv)
     next => rw [hF, represent_link]; have hu:= (norm_le_pi_norm b (pole (S.ratio.parent j.val.1,j.val.2))).trans hv; exact (hG _ (hu.trans hd)).trans (mul_le_mul_of_nonneg_left hu hA)
   exact (not_lt.mpr ((G.chord_triangle ..).trans (add_le_add ((hG _ (hx.trans hk)).trans (mul_le_mul_of_nonneg_left hx hA)) hv'))) hD
end YM.PhysicalNext.Repeat.Aroma
