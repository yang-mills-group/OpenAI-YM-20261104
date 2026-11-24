import YM.OPE.Compatible.Spades.Area
import YM.OPE.Compatible.Fathom.Cycle
import YM.Analysis.Exchange
/-!
# light smooth test hierarchy. amplitudes.B
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X] [NormedSpace ℝ X]
variable {I J:Type}{i j k r:ℕ}
local notation "Z"=> Radial.zone (E:=E)
abbrev Fline (p:E→ℝ)(v:Fin i→E)(x:E):= iteratedFDeriv ℝ i p x v
structure Stature (p:E→ℝ)(k:ℕ):Prop where
       smooth : ContDiff ℝ k p
       card {j:ℕ}(h:j≤k)(v:Fin j→E): Zone.Invoice Radial.zone (Fline p v)
lemma Fline_zero (p:E→ℝ)(v:Fin 0→E): Fline p v=p:= funext fun _=> iteratedFDeriv_zero_apply ..
variable {p q:E→ℝ}
lemma Stature.invoice (h: Stature p k): (Z).Invoice p:=by rw [← Fline_zero p (fun _=>0)]; exact (h.card (Nat.zero_le _) _)
lemma Stature.mono (h:Stature p k)(hp:i≤k):Stature p i:=⟨h.smooth.of_le (Nat.cast_le.mpr hp),fun hx=>h.card (hx.trans hp)⟩
lemma Stature.borne {a:ℕ→ℝ}(h:ContDiff ℝ k p)(he:∀ i≤k,∀ x, ‖iteratedFDeriv ℝ i p x‖ ≤ a i): Stature p k:=⟨h,fun {i} hi v=> Zone.Invoice.bounded (a i*∏ j,‖v j‖) (fun x=> ((iteratedFDeriv ℝ i p x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (he i hi x) (prod_nonneg fun _ _=> norm_nonneg _)))⟩
lemma rungs (h:ContDiff ℝ (j+1:ℕ) p)(v:Fin j→E)(x:E): Fline p (Fin.snoc v x)= Fline (pointD x p) v:=funext fun _=> Analysis.snoc_jet (h.contDiffAt) x v
lemma Stature.lower (h:Stature p (j+1))(v:E): Stature (pointD v p) j:=by
       refine ⟨contDiff_iff_contDiffAt.mpr (fun i=>Analysis.dSmooth h.smooth.contDiffAt v (by push_cast;rfl)),fun {i} hi x=>?_⟩; rw[← rungs (h.smooth.of_le (Nat.cast_le.mpr (by omega)))]; exact h.card (by omega) _
lemma statureUp (h: ContDiff ℝ (j+1:ℕ) p) (hq:(Z).Invoice p) (hp:∀ v:E,Stature (pointD v p) j): Stature p (j+1):=by
       refine ⟨h,fun {k} hk v=>?_⟩; cases k with
       | zero=> rw [Fline_zero]; exact hq
       | succ i=> rw [← Fin.snoc_init_self v,rungs (h.of_le (Nat.cast_le.mpr hk))]; exact (hp _).card (by omega) _
lemma FlAdd (h: ContDiff ℝ k p)(hp:ContDiff ℝ k q)(v:Fin k→E): Fline (p+q) v=Fline p v+Fline q v:=by funext i; unfold Fline; rw [iteratedFDeriv_add_apply h.contDiffAt hp.contDiffAt];rfl
lemma FlSub (h: ContDiff ℝ k p)(hp:ContDiff ℝ k q)(v:Fin k→E): Fline (p-q) v=Fline p v-Fline q v:=by funext i; unfold Fline; rw [iteratedFDeriv_sub_apply h.contDiffAt hp.contDiffAt];rfl
lemma Stature.add (h:Stature p k)(hp:Stature q k):Stature (p+q) k:=by refine ⟨h.smooth.add hp.smooth,fun {i} hi v=>?_⟩; rw [FlAdd (h.mono hi|>.smooth) (hp.mono hi|>.smooth)]; exact (h.card hi v).add (hp.card hi v)
lemma Stature.sub (h:Stature p k)(hp:Stature q k):Stature (p-q) k:=by refine ⟨h.smooth.sub hp.smooth,fun {i} hi v=>?_⟩; rw [FlSub (h.mono hi|>.smooth) (hp.mono hi|>.smooth),sub_eq_add_neg]; exact (h.card hi v).add (Zone.Invoice.weaken (hp.card hi v) (by simp))
lemma Stature.poly [FiniteDimensional ℝ E](h:Bond p) (k:ℕ):Stature p k:=by
       have he:= h.smooth.of_le (show (k:ℕ∞ω) ≤_ from le_top) -- may inf type
       induction k generalizing p with
       | zero=> exact ⟨he,fun {i} hi x=> by obtain rfl : i=0 := Nat.eq_zero_of_le_zero hi; rw [Fline_zero]; exact h.cost⟩
       | succ k ih=> exact statureUp he h.cost fun v=> ih (h.amount v) ((h.amount v).smooth.of_le le_top)
lemma Stature.pic (h:Stature p k){v:Fin i→E}(hp:i≤k): Continuous (Fline p v):= continuous_iff_continuousAt.mpr fun _=> Analysis.iterD ((h.mono hp).smooth.contDiffAt) _
lemma ringWheel (h:Stature p (j+1))(hp: Stature q (j+1))(v:E): pointD v (p*q)=p*pointD v q+q*pointD v p:=by
       funext x; unfold pointD; rw [fderiv_mul (h.smooth.differentiable (by simp) _) (hp.smooth.differentiable (by simp) _)];rfl
lemma Stature.mul (h:Stature p j)(hp:Stature q j):Stature (p*q) j:=by
       have hh:=h.smooth.mul hp.smooth; have ht:= h.invoice.mul hp.invoice; induction j generalizing p q with
       | zero=> refine ⟨hh,fun {i} hi v=>?_⟩; obtain rfl:=Nat.eq_zero_of_le_zero hi; rw [Fline_zero]; exact ht
       | succ j ih=>
            apply statureUp hh ht; intro v; change Stature (pointD v (p*q)) j; rw [ringWheel h hp]; apply Stature.add
            · exact ih (h.mono j.le_succ) (hp.lower v) ((h.mono j.le_succ|>.smooth).mul (hp.lower v|>.smooth)) ((h.mono j.le_succ|>.invoice).mul (hp.lower v|>.invoice)) -- maybe ih includes
            exact ih (hp.mono j.le_succ) (h.lower v) ((hp.mono j.le_succ|>.smooth).mul (h.lower v|>.smooth)) ((hp.mono j.le_succ|>.invoice).mul (h.lower v|>.invoice))
lemma CarriedL (h: (Z).Invoice p)(L:F→L[ℝ] E): Zone.Invoice (Radial.zone) (p ∘ L):=by
       obtain ⟨c,i,hc,H⟩:=h; refine ⟨c*(1+‖L‖)^i,i,by positivity,fun x=>?_⟩; apply (H (L x)).trans; rw [mul_assoc,←mul_pow]; apply mul_le_mul_of_nonneg_left _ hc; apply pow_le_pow_left₀ (zero_le_one.trans ((Z).high _)); change 1+‖_‖ ≤(1+‖L‖)*(1+‖x‖); nlinarith only [L.le_opNorm x,norm_nonneg L,norm_nonneg x]
lemma Stature.blot (h: Stature p k)(L:F→L[ℝ] E):Stature (p ∘ L) k:=by
       refine ⟨h.smooth.comp L.contDiff,fun {i} hi x=>?_⟩; rw[show Fline (p ∘ L) x=Fline p (L ∘ x) ∘ L from funext fun v=>DFunLike.congr_fun (L.iteratedFDeriv_comp_right h.smooth v (Nat.cast_le.mpr hi)) x]; exact CarriedL (h.card hi _) L
end YM.OPE.Jargon
