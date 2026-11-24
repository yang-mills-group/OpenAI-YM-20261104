import YM.OPE.Compatible.Cant.Hoe
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
abbrev Artπ (E:Type)[AddCommGroup E][Module ℝ E] := E→ₗ[ℝ] E→ₗ[ℝ] ℝ
abbrev ΦB (E:Type)[AddCommGroup E][Module ℝ E]:= Fin 3 → Artπ (Jewel E)
structure Job (G:Fin 3 → Artπ (Jewel E)):Prop where
     nil (x y:Jewel E):G 0 (τΓ E x) y=0∧ G 0 x (τΓ E y)=0
     one (x y:Jewel E):G 1 (τΓ E x) y=G 0 x y∧ G 1 x (τΓ E y)=G 0 x y
     two (x y:Jewel E):G 2 (τΓ E x) y=G 1 x y∧ G 2 x (τΓ E y)=G 1 x y
structure Svet (Y:ℕ→ ΦB E)(F:Jewel E→ₗ[ℝ] Jewel E)(u:ℝ): Prop where
      drum : Job (Y 0)
      fuel (n:ℕ)(t:Fin 3)(x y:Jewel E): Y (n+1) t x y=Y n t (F x) (F y)
      capT (x:Jewel E):F x 0=u • (x 0)
      slip(p:Jewel E):F (τΓ E p)= τΓ E (F p)
      winds (p q:Jewel E):Y 0 1 (F p) (F q)=u*u*Y 0 1 p q
      earn (x:E)(hp:x≠0):0 < Y 0 0 (Pi.single 0 x) (Pi.single 0 x)
-- explicit algebra
omit [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma sloshL {R F:Type}[AddCommGroup R][Module ℝ R][AddCommGroup F][Module ℝ F](g:R→ₗ[ℝ] F)(h:Artπ F): ∃ f:Artπ R,∀ x y,f x y=h (g x) (g y):=⟨LinearMap.compl₂ (h.comp g) g,fun _ _=>rfl⟩
end YM.OPE.Hark
