import YM.FormalBulk08.Orb.Sapphire

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V] (H : Hull V I)

def lever (p : Pap (V⊕I)) := PowerSeries.map (MvPolynomial.aeval (R:=ℝ)
   (Sum.elim (fun i:V=> MvPolynomial.X (Sum.inl (β:=I) i)+MvPolynomial.rename Sum.inr (H.drift i)) (fun i:I=> MvPolynomial.X (Sum.inr i)))).toRingHom p

def cobalt (p : Pap (V⊕I)) := lever H p - C (coeff 0 (lever H p))
lemma cobalt_base (p) : coeff 0 (cobalt H p)=0 := by simp [cobalt]
lemma fuel_emer (p) : toInk H p=PowerSeries.map (emer V I).toRingEquiv.toRingHom (lever H p) := by
   unfold toInk roam lever; rw [← RingHom.comp_apply, ← map_comp]
   rw [show insertAt ℝ (fueled H)=C.comp ((emer V I).toRingEquiv.toRingHom.comp _) from ?hex,pure_map]
   case hex=>
      ext
      case hC r n m l=> simp [emer]
      case hX i n m l=>
         cases i with
         | inl i=>
            have hh : emer V I (MvPolynomial.rename Sum.inr (H.drift i))= MvPolynomial.C (H.drift i) := DFunLike.congr_fun (MvPolynomial.sumAlgEquiv_comp_rename_inr ℝ V I) (H.drift i)
            unfold emer at hh; simp [emer,fueled,boost,hh]
         | inr i=>simp [fueled,boost,emer]
lemma cobalt_positive (p) (hp : Solved H p) : PowerSeries.map (emer V I).toRingEquiv.toRingHom (cobalt H p)=positive H p := by
   have he:=hp; unfold Solved at he; rw [fuel_emer,coeff_map] at he
   rw [cobalt,map_sub,positive,←fuel_emer,PowerSeries.map_C,he,boost,PowerSeries.map_C,map_add]; abel
variable [Fintype I]
lemma output_sky (p) (hp : Solved H p) : out H p=C H.main + PowerSeries.map (aftEval V I).toRingHom (late (coal (aqua H.saddle) (cobalt H p))) := by
   unfold out vocal; rw [←cobalt_positive H p hp,←map_expan _ (cobalt_base H p),moment_aqua,← coal_recovers _ _ (cobalt_base H p)]
   have hz:=coal_base (aqua H.saddle) _ (cobalt_base H p)
   unfold late; rw [map_expan _ hz,map_expan _ (by rw [coeff_map,hz,map_zero]), covelog_after (by rw [coeff_map,coeff_map,hz,map_zero,map_zero])]
lemma tag_sky (p t) (hp : Solved H p) : flag H p t= PowerSeries.map (aftEval V I).toRingHom (late (flare (aqua H.saddle) (cobalt H p) (lever H t))) := by
   apply ((expan_after (voice H p hp)) ▸ expan_unit (covelog_rank (voice H p hp)) : IsUnit (vocal H p)).mul_right_inj |>.mp
   rw [normalization _ _ hp]; rw [←cobalt_positive H p hp,fuel_emer H t,←map_expan _ (cobalt_base H p), ←map_mul,moment_aqua]
   conv_rhs => arg 1; unfold vocal; rw [←cobalt_positive H p hp,←map_expan _ (cobalt_base H p),moment_aqua]
   rw [←map_mul,flare_denominator (aqua H.saddle) _ _ (cobalt_base H p)]
end YM.FormalBulk08.Orb
