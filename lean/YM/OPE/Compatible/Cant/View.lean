import YM.OPE.Compatible.Cant.Qu
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
variable {μ:ℕ→ℝ}{Φ:(e:Fin d)→ ℕ→ ΦB (V e)}
noncomputable abbrev Buck (x:M) [∀ i,FiniteDimensional ℝ (V i)] := (bulk R x).toContinuousLinearMap
structure Stamp (μ:ℕ→ℝ)(Φ:(e:Fin d)→ℕ→ ΦB (V e))(T:Mel V→ₗ[ℝ] Mel V)(i:ℕ) :Prop where
     trips (p:Mel V): T (FlowP V p)= FlowP V (T p)
     gear(e:Fin d)(p:Jewel (V e)): (PDiag T e p) 0=(μ e.val)^i • p 0
     costT (e:Fin d)(p q:Jewel (V e))(t:Fin 3): Φ e i t p q=Φ e 0 t (PDiag T e p) (PDiag T e q)
     upper (e:ℕ)(ht:e≤ d)(p:Mel V)(h:trims e p): trims e (T p)
variable {κ:M→ ℝ}
lemma Bucks [∀ i,FiniteDimensional ℝ (V i)](h:Charge H κ): Wealth (fun x=> Buck (R:=R) x) κ 1:=by
       apply Scooped (fun i=> bulk R i) (fun x=>?_) h.keep zero_le_one; simp_rw[bulk_way]; exact wealthset Finset.univ _ (fun i _=> h.blu i id (fun _=>1) (fun _=>x i) (wealthC _)) h.keep zero_le_one
end Pipes
end YM.OPE.Hark
