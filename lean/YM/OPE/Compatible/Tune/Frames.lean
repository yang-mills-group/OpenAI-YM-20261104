import YM.OPE.Compatible.Tune.Fares
import YM.OPE.Compatible.Cant.View
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
variable {W:Fin d→Type}[∀ i,NormedAddCommGroup (W i)][∀ i,NormedSpace ℝ (W i)]
variable (f:(i:Fin d)→Jewel (V i)≃ₗ[ℝ] Jewel (W i))(g:(i:Fin d)→ V i≃ₗ[ℝ] W i)(hp:∀ i,Honest (f i) (g i))
open Pipes
-- lin equiv Mel
noncomputable def honors : Mel V≃ₗ[ℝ] Mel W:= LinearEquiv.piCongrRight f
lemma hway (x:Mel V)(i:Fin d): honors f x i=f i (x i):=rfl
lemma bway (x:Mel W)(i:Fin d): (honors f).symm x i=(f i).symm (x i):=rfl
noncomputable abbrev Uptake (U:Mel V→ₗ[ℝ] Mel V): Mel W→ₗ[ℝ] Mel W:= (honors f).toLinearMap.comp (U.comp (honors f).symm.toLinearMap)
lemma LedLine (U:Mel V→ₗ[ℝ] Mel V)(e:Fin d):PDiag (Uptake f U) e= Kw (f e) (PDiag U e):=by
       apply LinearMap.ext; intro x; suffices he:(honors f).symm (Pi.single e x)= Pi.single e ((f e).symm x) by
          change f e (U _ e)= _; erw [he]; rfl
       funext j; by_cases h:j=e; subst j; rw [bway,Pi.single_eq_same,Pi.single_eq_same]; rw [bway,Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; exact map_zero _
include hp
lemma troop (x:Mel V): honors f (FlowP V x)=FlowP W (honors f x):=funext fun i=>(hp i).comm _
lemma troup (x:Mel W):(honors f).symm (FlowP W x)=FlowP V ((honors f).symm x):=funext fun i=> (hp i).inv.comm _
variable {Φ:(e:Fin d)→ℕ→ ΦB (V e)}{i:ℕ}{T:Mel V→ₗ[ℝ] Mel V}{μ:ℕ→ℝ}
abbrev BQuest (Y:(e:Fin d)→ℕ→ΦB (V e)): (e:Fin d)→ℕ→ ΦB (W e):=fun i n=> Lore (f i) (Y i) n
lemma renameS (h:Pipes.Stamp μ Φ T i):Stamp μ (fun e r=>Jug (f e) (Φ e r)) (Uptake f T) i:=by
       let X:=honors f; refine ⟨fun p=> ?_,fun e p=>?_,?_,?_⟩
       · change X (T (X.symm (FlowP W p)))=FlowP W (X _); rw [show X.symm (FlowP W p)=_ from troup f g hp _,h.trips, show X (FlowP V _)=_ from troop f g hp _]; rfl -- Flow .. _ syntax
       · rw [LedLine,KwRun,(hp _).earns,h.gear,(g e).map_smul,(hp e).inv.earns,(g e).apply_symm_apply]
       · intro e p q j; rw [JugEq,JugEq,h.costT e,LedLine]; simp_rw[KwRun,(f e).symm_apply_apply]
       intro i' hi x hx j hj; have hp':trims i' (X.symm x):=fun i hi=>by change (f i).symm (x i)=0;rw [hx i hi,map_zero]
       change f j (T (X.symm x) j)=_; rw [h.upper i' hi (X.symm x) hp' _ hj,map_zero]
lemma transS (h: Stamp μ Φ T i): Stamp μ (BQuest f Φ) (Uptake f T) i:=by
       apply renameS f g hp; exact ⟨h.trips,h.gear,fun e p q t=>by erw [symEq (Φ e i t) p q,symEq]; simp_rw [h.costT (V:=V)],h.upper⟩
end YM.OPE.Hark
