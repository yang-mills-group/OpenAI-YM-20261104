import YM.FVA2.ColorCoordinates
/-!
# Taylor stencil identification for log link and octet pairs

All structures built from the pinned BV density, no estimator. Unmarked part
and insertions use the **same real analytic chart**. For tuning, apply ONLY
 common formal substitution afterwards. Track total advancements exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.PairCoords
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Chart
open Function Filter Metric MeasureTheory TreeBasis Trans
open Wilson Based GaussianScore MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare MS.Plane MS.Landau MS.Koszul
open Modes MS.Native MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native.Draft MS.Native.Wilsonian MS.Native.Chart MS.Puff MS.Puff.Engine MS.Puff.Mom MS.Book MS.Book.Program MS.Bare.Focus Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {U J:Type} {n:Side}
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
def bell : Slot U J → Wilson.Field G n := Sum.elim m (fun _=>0)
lemma bell_even (i : Slot U J)(h: φ i=true): bell m i=0:= by rcases i with _|i; contradiction; rfl

def LMap (G:Gauge) (n:Side): Wilson.Field G n →L[ℝ] City G (Site n) :=
   (coverL G n ∘ₗ (plan G n).L).toContinuousLinearMap
lemma bosDir (i:Slot U J) : (LMap G n ∘ bell m) i = ∑ j:Pos G n, plugIn m b i j • Native.direction j:= by
   rcases i with i|⟨j|j⟩; rotate_left
   · simp only [Fintype.sum_prod_type,Fintype.sum_option, plugIn,direction,zero_smul,smul_zero,Finset.sum_const_zero,add_zero, Fintype.sum_bool]; -- `sum_bool` after prod
     exact map_zero _
   · simp only [Fintype.sum_prod_type, plugIn,direction,zero_smul,smul_zero,Finset.sum_const_zero,add_zero, Fintype.sum_bool]; exact map_zero _
   simp only [Fintype.sum_prod_type,Fintype.sum_option, plugIn,direction,smul_zero,Finset.sum_const_zero,zero_add,Fintype.sum_bool]
   let F:= LMap G n (m i); have hv:= Native.frame F; change F=_; apply Eq.trans hv.symm; simp only [Fintype.sum_prod_type, projector_k]; -- sum order x,i,k vs i,k,x
   rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> Finset.sum_comm

theorem pin_read {f:City G (Site n) → ℝ} (h:germ f) :
    plug (mkPlug m b) (reads f) = ink (bell m) (f ∘ LMap G n):= by
   rw [Taylor.ink_ctrl_one _ _ h, Taylor.scale_pos _ (LMap G n ∘ bell m) (plugIn m b) (bosDir m b) h]; rfl
lemma cap_stem (h:ℤ) (F:BL (Pos G n)): plug (mkPlug m b) (mask h F)=mask h (plug (mkPlug m b) F):= by
   change plug (mkPlug m b) (MS.Book.model h (region.symm F)).val= _
   rw [plug_cyl]; exact (mod_ink (region.symm F) (mkPlug m b))
lemma atLetter_erase (x:Pos G n) (h:∀ j:Slot U J, plugIn m b j x=0): plug (mkPlug m b) (atLetter x)=0:= by
   apply ext_D; rfl
   intro i; change D _ (plug _ (Cylinder.single (R:=ℂ) _).val)=_
   rw [plug_cyl, Cylinder.names]; simp [mkPlug,h]
section letter
variable [Fintype U][Fintype J]
private lemma atLetter_combine (x:Pos G n): plug (mkPlug m b) (atLetter x)=∑ i:Slot U J,mkPlug m b i x • atLetter i:= by
   apply ext_D; · rw [plug_nil,Finset.sum_apply]; simp [atLetter]
   intro i; change D _ (plug _ (Cylinder.single (R:=ℂ) _).val)=_; rw [plug_cyl, Cylinder.names,map_sum]; rw [Finset.sum_eq_single i];
   · rw [map_smul,Cylinder.hear]
   · intro j _ hj; rw [map_smul,Cylinder.unheard _ (Ne.symm hj),smul_zero];
   simp
lemma ghostPlug (i:G.ColorIndex) (x : Site n): plug (mkPlug m b) (GH i x).val=∑ j:J,(ghostC b j x i:ℂ) • atLetter (c j):= by
    rw [ show (GH i x).val=atLetter (SiteC i,x) from rfl, atLetter_combine, Fintype.sum_sum_type, Fintype.sum_sum_type ]; simp only [mkPlug, plugIn,Complex.ofReal_zero, zero_smul,Finset.sum_const_zero,zero_add,add_zero]
lemma kPlug (i:G.ColorIndex)(x:Edge (Site n)): plug (mkPlug m b) (AHplus i x).val= ∑ j:J,(kField b j x i:ℂ) • atLetter (bar j):= by
    rw [ show (AHplus i x).val=atLetter (KV x.2 i,x.1) from rfl, atLetter_combine, Fintype.sum_sum_type,Fintype.sum_sum_type]; simp only [mkPlug, plugIn,Complex.ofReal_zero, zero_smul,Finset.sum_const_zero,zero_add]
end letter

lemma costing (A: _root_.YM.Wilson.Config G n → ℝ) : (A ∘ assemble G n) ∘ (plan G n).L=(A ∘ expLinks G _) ∘ LMap G n:= by
    funext x; exact congr_arg A (assemble_exp G n _)

theorem plug_weight : plug (mkPlug m b) (pay true • (sumHome (weightW G (drive n) 0)).val)= -(ink (bell m) (WilsonPull (plan G n))) := by
   rw [map_smul,allWeight,show ink (glow G (Site n)).e0 (Native.Chart.rent (drive n))=reads (Native.Chart.rent (drive n)) from rfl, pin_read _ _ (rent_s (drive n))];
   have hv : (rent (G:=G) (drive n)) ∘ LMap G n=(- (2:ℝ)) • (WilsonPull (plan G n)):= by
      funext x; rw [Function.comp_apply,original_W]; unfold WilsonPull pricing; rw [Pi.smul_apply, Function.comp_apply]; rw [assemble_exp]; change -(_root_.YM.Wilson.energy _) = (-2:ℝ)*(_root_.YM.Wilson.energy (nation ((LMap G n) x)) / 2); ring
   rw [hv, ink_smul _ (pull_hot (plan G n)),smul_smul]; rw [show pay true * Complex.ofReal (- (2:ℝ)) = -1 from (by unfold pay; norm_num), neg_one_smul ]
end YM.FVA2.PairCoords
