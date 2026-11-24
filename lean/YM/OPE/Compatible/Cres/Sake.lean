import YM.OPE.Compatible.Nut.Hero
/-! # energy jets perturb clocks before brightness -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift Pipes
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q I:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)][∀ i,FiniteDimensional ℝ (V i)]
-- V space.E affine broadcast
noncomputable def PlaS (V:Fin d→Type)[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)](j:Fin 3): Mel V→L[ℝ] Mints V:= ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj j ∘L ContinuousLinearMap.proj i)
omit [∀ i,FiniteDimensional ℝ (V i)] in
lemma filmW (v:Mel V)(q:ℝ): FilmP V q v= PlaS V 0 v+q • PlaS V 1 v+q^2 • PlaS V 2 v:=rfl
omit [∀ i,FiniteDimensional ℝ (V i)] in
lemma Wl (x:Mel V)(q:ℝ): FilmP V q (FlowP V x)= q • FilmP V q x -q^3 • PlaS V 2 x:=by
        funext i; change (0:V i)+q • x i 0+q^2 • x i 1= q • (x i 0+q • x i 1+q^2 • x i 2)- q^3 • x i 2; simp only[smul_add,smul_smul,zero_add]; module -- inspect
omit [∀ i,FiniteDimensional ℝ (V i)] in
lemma ΔΔz (x:Mel V): x= Junit V (PlaS V 0 x)+ FlowP V (Junit V (PlaS V 1 x))+ FlowP V (FlowP V (Junit V (PlaS V 2 x))):=by
        funext i j; have h(i:Fin d): x i= (Pi.single 0 (x i 0): Jewel _) + τΓ _ (Pi.single 0 (x i 1))+ τΓ _ (τΓ _ (Pi.single 0 (x i 2))):=(τwrite (x i)).symm; exact congr_fun (h i) j -- ψ
variable (T:Mel V→L[ℝ] Mel V)(h:∀ v:Mel V,T (FlowP V v)= FlowP V (T v))
omit [∀ i,FiniteDimensional ℝ (V i)] in
include h in
lemma Beyond (q:ℝ)(x:Mel V) :
        let u(j:Fin 3):= Junit V (PlaS V j x);
        FilmP V q (T x)-border q T.toLinearMap (FilmP V q x)= -q^3 • PlaS V 2 (T (u 1)) - q^4 • PlaS V 2 (T (u 2))- q^3 • PlaS V 2 (FlowP V (T (u 2))):=by
           intro u; let L:= border q T.toLinearMap; let b:=FilmP V q; have he : b (T x)= b (T (u 0))+b (FlowP V (T (u 1)))+b (FlowP V (FlowP V (T (u 2)))):=(by rw [show T x=T (u 0)+T (FlowP V (u 1))+ T (FlowP V (FlowP V (u 2))) from (by rw [←map_add,←map_add];exact congr_arg _ (ΔΔz ..)),h,h,h,b.map_add,b.map_add]); have ht : L (b x)= b (T (u 0))+q • b (T (u 1))+q^2 • b (T (u 2)):=by rw [show b x= _ from filmW x q,L.map_add, L.map_add,L.map_smul,L.map_smul];rfl
           change b (T x)- L (b x)= _; rw [he,ht,show b _=_ from Wl (T (u 1)) q,show b (FlowP V (_))=_ from Wl (FlowP V (T (u 2))) q, Wl]; module
-- include h res. Camera.W
end YM.OPE.Hark
