import YM.OPE.Compatible.Tune.Hem
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {i j m:ℕ}{μ:ℝ}{U:Jewel E→ₗ[ℝ] Jewel E}{V:ℕ→ ΦB E}{k:E≃ₗ[ℝ] F}
-- Euclidean Frame.Sym
variable {d:ℕ}
structure Auth (V:ℕ→ ΦB (Dryst d))(U:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d))(μ:ℝ) :Prop where
     gauge : Svet V U μ
     core (x y:Jewel (Dryst d)):V 0 0 x y= inner ℝ (x 0) (y 0)
     tilt (x y:Dryst d): V 0 1 (τ₀ (Dryst d) x) (τ₀ (Dryst d) y)=0
variable [FiniteDimensional ℝ E]
noncomputable abbrev Lore (f:Jewel E≃ₗ[ℝ] Jewel F)(V:ℕ→ ΦB E)(i:ℕ):ΦB F:= Jug f (fun j=> Tot (V i j))
omit [FiniteDimensional ℝ E] in lemma StickR (X:E≃ₗ[ℝ] F) (v:F): (τequi X).symm (τ₀ F v)= τ₀ E (X.symm v):=by
      suffices h:∀ j:Fin 3, X.symm (τ₀ F v j)=τ₀ E (X.symm v) j from funext h; intro j; by_cases e:j=0; subst j; rw[τat,τat]; have ht:(τ₀ E) (X.symm v) j=0:=Pi.single_eq_of_ne e _; rw[ht,show τ₀ F v j=0 from (by simp [τ₀,Ne.symm e]),X.symm.map_zero] -- unused
lemma albora (H:Svet V U μ) :∃ (f:Jewel E≃ₗ[ℝ] Jewel (Brane E)) (k:E≃ₗ[ℝ] Brane E), Honest f k∧ Auth (Lore f V) (Kw f U) μ:=by
     let W(i:ℕ)(j):= Tot (V i j); have ht:=ampW H; obtain ⟨k,hK⟩:= quarkX (originω (W 0 0)) (fun x y=> symmTran _ _ _) ht.earn; obtain ⟨M,hM⟩:= curvature _ ht.drum ht.earn (fun i x y=> symmTran ..); let f:= (LoopΘ M).symm.trans (τequi k); have h:Honest f k:=honestTrans _ _ _ (Honest.τ k) (honestLoop M).inv -- change
     refine ⟨f,k,h,h.live ht,fun x y=>?_,fun x y=>?_⟩
     · unfold Lore; rw [JugEq,(ampW H).drum.top,h.inv.earns,h.inv.earns]; exact (hK (k.symm (x 0)) (k.symm (y 0))).trans (by rw[k.apply_symm_apply,k.apply_symm_apply])
     unfold Lore; rw [JugEq]; have he(z:Brane E):f.symm (τ₀ _ z)=LoopΘ M (τ₀ E (k.symm z)):=congr_arg (LoopΘ M) (StickR k z); rw [he,he]; exact hM (k.symm x) (k.symm y)
end YM.OPE.Hark
