import YM.OPE.Compatible.Tune.Frames
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
open Pipes
noncomputable abbrev Junit (V:Fin d→ Type)[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]: ((i:Fin d)→ V i)→ₗ[ℝ] Mel V:= LinearMap.pi (fun k:Fin d=> (τ₀ (V k)).comp (LinearMap.proj k))
noncomputable abbrev FilmP (V:Fin d→Type)[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)](r:ℝ):Mel V→ₗ[ℝ] ((i:Fin d)→ V i):= LinearMap.pi (fun k=> (Filmμ r).comp (LinearMap.proj k))
noncomputable abbrev border (r:ℝ)(T:Mel V→ₗ[ℝ] Mel V): Mints V→ₗ[ℝ] Mints V:= (FilmP V r).comp (T.comp (Junit V))
-- overriding frame cutoff index d.
variable {Φ:(i:Fin d)→ ℕ→ ΦB (V i)}{T:Mel V→ₗ[ℝ] Mel V}{Z:ℕ→ℝ}{i j:ℕ}
lemma coordH (e:Fin d)(x:V e)(p:ℝ): (border p T) (Pi.single e x) e=κeval p (PDiag T e) x:=by
       change Filmμ p (T (Junit V (Pi.single e x)) e)= Filmμ p (T (Pi.single e ((τ₀ (V e)) x)) e); rw [show Junit V (Pi.single e x)= Pi.single e ((τ₀ (V e)) x) from ?_] ; funext j; by_cases h:j=e; subst j; change τ₀ (V e) ((Pi.single e x : Mints V) e)= _; erw[Pi.single_eq_same,Pi.single_eq_same]; change τ₀ (V j) ((Pi.single e x : Mints V) j)= _; erw[Pi.single_eq_of_ne h, Pi.single_eq_of_ne h,map_zero]
lemma Scope (h:Stamp Z Φ T j)(p:Mints V)(x:ℕ)(hp:trims x p)(hx:x ≤ d)(r:ℝ):trims x (border r T p):=by
       have he:trims x (Junit V p):=fun k hk=> by change τ₀ (V k) (p k)=0;rw [hp k hk,map_zero]
       intro k hk; change Filmμ r (T (Junit V p) k)=0; rw[h.upper _ hx _ he _ hk,map_zero]
variable {σ:Fin d→ℕ}
local notation "C!"=>fun i: Fin d=>Dryst (σ i)
lemma PortCost (U:(i:Fin d)→ℕ→ ΦB (Dryst (σ i)))(K:(i:Fin d)→ Jewel (Dryst (σ i))→ₗ[ℝ] Jewel (Dryst (σ i)))(h:∀ i,Auth (U i) (K i) (Z i.val))(hp:∀ i,Z i>0):∃ f:ℝ,1 ≤ f∧∀ (i:Fin d)(j:ℕ)(T: Mel (C!)→ₗ[ℝ] Mel (C!)),Stamp Z U T j →∀ x:Dryst (σ i),∀ r:ℝ,|r|≤1 → |‖border r T (Pi.single i x) i‖^2-(Z i.val^j*‖x‖)^2|≤(j*(Z i.val^j)^2*f*r^2+|r|^3*3*(ζCost (PDiag T i))^2)*‖x‖^2:=by
       choose k hk hK using fun i=>soar (h i); let x:= ∑ i,k i; have hv:0≤x:=Finset.sum_nonneg fun i _=>zero_le_one.trans (hk i); have he (i):k i≤1+x:= (Finset.single_le_sum (f:=k) (fun i _=> zero_le_one.trans (hk i)) (Finset.mem_univ _)).trans (by linarith); refine ⟨1+x,(by linarith),fun i j T ht v r hr=>?_⟩
       have hH:Clamp j (Z i.val) (PDiag T i) (U i):=⟨fun x=>by rw [ht.gear,τat],fun x v => (ht.costT i (τ₀ _ x) (τ₀ _ x) v).symm⟩; rw [coordH]; apply (hK i j _ hH v r hr (hp i.val)).trans; gcongr; exact he i
end YM.OPE.Hark
