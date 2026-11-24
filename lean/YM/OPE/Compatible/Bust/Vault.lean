import YM.OPE.Compatible.Bust.Airy
/-!
# transfer. Seat (<∞). 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char
open scoped Topology BigOperators Classical
variable {I K E:Type}{m r i j n k:ℕ}{C D:ℝ}
-- continuity of script value
section
variable [Fintype I]{S:Side}
omit [Fintype I] in
lemma tiller (m:ℕ)(p:stave m i I): Summable (seed m _ _ p):= sootS (humor p)
lemma gearL (m:ℕ)(i:ℕ)(x:Site S): ∃ A:stave m i I→L[ℝ] Pole (deck I S) i, ‖A‖≤1∧∀ p,A p=orchestra (seed m i I p) x:=by
      let f(p:stave m i I):=orchestra (seed m _ _ p) x; let P(p):=seed m i I p
      have he(p v): f p v=scribe x (P p) v:=(instruments _ (tiller _ _) ..).tsum_eq.symm
      let A:stave m i I→ₗ[ℝ] Pole (deck I S) i:={
                             toFun:=f
                             map_add' :=by intro a b;ext1 v; rw [_root_.add_apply,he,he,he]; unfold P; rw [map_add]; change (∑' i,(P a i+P b i)*render x i v)=_; simp_rw [add_mul]; exact (instruments _ (tiller _ a) x v).summable.tsum_add (instruments _ (tiller _ b) x v).summable -- need p
                             map_smul' :=by intro a p; ext1 v; rw [_root_.smul_apply,he,he]; unfold P; rw [map_smul]; exact score_scaled x (seed m i I p) v a }
      have ht(p:stave m i I):‖A p‖≤ 1*‖p‖:=by
           rw [one_mul]; let g(i):= P p i • each_line x i; have hv(t:Page I i):‖g t‖≤ ‖P p t‖:=by unfold g; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (easily ..)
           let h:=Sack.mass (humor (m:=m) p) (payer m); have hs: Summable (fun i=>‖g i‖):= h.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) hv
           exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hv h.2.1).trans h.2.2)
      let D:=A.mkContinuous 1 ht; exact ⟨D,D.opNorm_le_bound zero_le_one ht,fun _=>rfl⟩
noncomputable def reading (m i:ℕ)(p:Site S): stave m i I→L[ℝ] Pole (deck I S) i:= (gearL (I:=I) m i p).choose
lemma readsF (m i:ℕ)(p: Site S):‖reading (I:=I) m i p‖ ≤ 1:= (gearL m i p).choose_spec.1
lemma toScript (m i:ℕ)(p: Site S)(x:stave m i I): reading m i p x=orchestra (seed m i I x) p:= (gearL m i p).choose_spec.2 x
end
noncomputable def moduleAt (m k r:ℕ)(I:Type): Seat k m I→L[ℝ] stave m r I:= if h:r≤ k then ContinuousLinearMap.proj (⟨r,by omega⟩:Fin (k+1)) else 0
noncomputable def lilies (m k:ℕ)(I:Type): Seat k m I→ₗ[ℝ] Curtain I:= LinearMap.pi fun i=>(seed _ _ _) ∘ₗ (moduleAt m k i I).toLinearMap
lemma soup (x:Seat k m I)(i:ℕ): lilies m k I x i=seed m i I (moduleAt m k i I x):=rfl
lemma lemon (i:ℕ)(x:Seat k m I): ‖moduleAt m k i I x‖ ≤ ‖x‖:=by
     unfold moduleAt; split; next h=> exact norm_le_pi_norm x _
     simpa only [_root_.zero_apply,norm_zero] using norm_nonneg x
lemma sproutV (m k:ℕ)(x:Seat k m I): Volume (lilies m k I x) k m ‖x‖:=by
     refine ⟨fun i hi=>?_,fun i=>Sack.tips (humor (moduleAt m k i I x)) (lemon _ _)⟩; rw [soup,moduleAt,dif_neg (not_le.mpr hi),_root_.zero_apply,map_zero]
noncomputable def fundus (p:Curtain I)(L:ℝ)(h:Volume p k m L): Seat k m I:= fun i=> plant m (p i.val) L (h.2 _)
lemma sproutsX (p:Curtain I)(h:Volume p k m C): lilies m k I (fundus p C h)=p:=by
      funext i; rw [soup,moduleAt]; split; next he=> exact botany m (p i) C (h.2 _)
      next he=> rw [_root_.zero_apply,map_zero,h.1 i (by omega)]
lemma sproutsU (p:Curtain I)(h:Volume p k m C): ‖fundus p C h‖ ≤ C:= (pi_norm_le_iff_of_nonneg ((Sack.coins (h.2 0)))).mpr fun i=>kept_stalk (h.2 i.val)
lemma lilies_inj (I:Type)(k m:ℕ): Injective (lilies m k I):=by
      intro a b h; funext i; have he:= congr_fun h i.val; simp_rw [soup,moduleAt,dif_pos (Nat.le_of_lt_succ i.isLt)] at he; exact seed_inj m i.val I he
section
variable [Fintype I]{S:Side}
noncomputable def worldR (m k:ℕ)(x:Site S)(I:Type)[Fintype I]:Seat k m I→ₗ[ℝ] Song (deck I S):= LinearMap.pi fun i=>(reading m i x).toLinearMap ∘ₗ (moduleAt m k i I).toLinearMap
end
end YM.OPE.Silt.Float
