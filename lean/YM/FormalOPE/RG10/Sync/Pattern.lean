import YM.FormalOPE.RG10.Sync.Stability
/-!
 # polynomial representation of time-independent pull & frame shift
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {I B:Type}[Fintype I] [Fintype B]
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable (L:Layout I E)(Q: Layout B F)
 def across : Layout (I⊕B) (E×F) where
 toFun v:= Sum.elim (L v.1) (Q v.2)
 invFun v:= (L.symm (v ∘ Sum.inl), Q.symm (v ∘ Sum.inr))
 map_add' x y:= funext fun i=> by cases i<;>simp
 map_smul' r x:= funext fun i=> by cases i<;>simp
 left_inv x:= by change (L.symm (L x.1), Q.symm (Q x.2))=x; simp
 right_inv x:=funext fun i=> by cases i<;>simp
omit [Fintype I] [Fintype B] in
@[simp] lemma colored (x y): tint (across L Q) (x,y)= Sum.elim (tint L x) (tint Q y):= funext fun i=> by cases i<;>rfl

variable (u:F→ₗ[ℝ] E)
 def feature (i:I): Module.Dual ℝ E:= (LinearMap.proj i) ∘ₗ L.toLinearMap
 def strand (i:I): Packet B:= stroke Q ((feature L i) ∘ₗ u)
 def pulling(P:Ticket E):= digital Q (boost u P)
omit [Fintype I] in
lemma adjunction (p:Packet I)(x:F): MvPolynomial.aeval (tint Q x) (MvPolynomial.aeval (strand L Q u) p)=MvPolynomial.aeval (tint L (u x)) p:= by
 have he : ((MvPolynomial.aeval (tint Q x): Packet B→ₐ[ℂ] ℂ).comp (MvPolynomial.aeval (strand L Q u)))= (MvPolynomial.aeval (tint L (u x)):Packet I →ₐ[ℂ] ℂ) := by ext i; simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]; exact stencil Q _ _
 exact AlgHom.congr_fun he _

 def spurs (j:I):Channel B:= PowerSeries.C (strand L Q u j)
 def uprightC : Packet B →ₐ[ℂ] Channel B where
 __:= PowerSeries.C (R:=Packet B)
 commutes' _:= (PowerSeries.algebraMap_apply).symm
omit [Fintype I] in
lemma constants (p:Packet I): MvPolynomial.aeval (spurs L Q u) p = uprightC (B:=B) (MvPolynomial.aeval (strand L Q u) p):= by
 have he: (MvPolynomial.aeval (spurs L Q u):Packet I→ₐ[ℂ] Channel B)= uprightC.comp (MvPolynomial.aeval (strand L Q u)):= by ext i; simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl
 exact AlgHom.congr_fun he _
omit [Fintype I] in
lemma thread (p:Channel I): replot (spurs L Q u) p= PowerSeries.map (MvPolynomial.aeval (strand L Q u): Packet I→ₐ[ℂ] Packet B) p:= by
 apply PowerSeries.ext; intro i; rw [replot_coeff, PowerSeries.coeff_map];
 rw [Finset.sum_eq_single (i,0)];
 · simp [constants, uprightC]; try rfl
 · intro b hi he; have ht:= Finset.mem_antidiagonal.mp hi; have hp:b.2≠0:= by rintro e; exact he (Prod.ext (by show b.1=i;omega) e)
   rw [constants]; change coeff b.2 (C _) = _; simp [coeff_C,hp]
 simp
lemma reassess (P:Ticket E): replot (spurs L Q u) (digital L P)= digital Q (boost u P):= by
 apply PowerSeries.ext; intro i; apply recognise Q; intro x; rw [thread]; simp only [boost,digital,PowerSeries.coeff_map]
 change MvPolynomial.aeval (tint Q x) (MvPolynomial.aeval (strand L Q u) (ink L _))=_; rw [adjunction, expresses,expresses]; rfl
end YM.FormalOPE.RG10.Sync
