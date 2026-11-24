import YM.OPE.Compatible.Cres.Woe
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
open Stroke
variable (S:I→Mel V →L[ℝ] Mel V) (Y:I→Mel V) {u:ℝ}{L:Filter I}{T W':I→ℝ}(hL:Tendsto T L atTop)(hf:RateLE L T Y 0)(ht:RateLE L T S 0)(hs:∀ᶠ i in L,∀ x: Mel V,S i (FlowP V x)=FlowP V (S i x))(hZ:RateLE L T W' u)(hu':u ≤ 0)
include hL hf ht hs hZ hu'
lemma φPole : RateLE L T (fun i=> FilmP V (W' i) (S i (Y i))- border (W' i) (S i).toLinearMap (FilmP V (W' i) (Y i))) (3*u):=by
       let P(j:Fin 3)(i:I):=Junit V (PlaS V j (Y i)); have hp(j):RateLE L T (fun i=>P j i) 0:=by
             have hz(t:Fin 3): RateLE L T (fun i=> PlaS V t (Y i)) 0:= (rakeQ (hf) (RateLE.const (PlaS V t) hL)).mono (by simp)
             exact (rakeQ (hz j) (RateLE.const (Junit V|>.toContinuousLinearMap) hL)).mono (by simp)
       let A:= PlaS V 2; have hu(j:Fin 3):RateLE L T (fun i=> S i (P j i)) 0:= (rakeQ (hp j) ht).mono (by simp); have hv(j:Fin 3): RateLE L T (fun i=> A (S i (P j i))) 0:=(rakeQ (hu j) (RateLE.const A hL)).mono (by simp)
       have he: RateLE L T (fun i=>A (FlowP V (S i (P 2 i)))) 0:=(rakeQ (hu 2) (RateLE.const (A ∘L (FlowP V).toContinuousLinearMap) hL)).mono (by simp)
       refine ((((hZ.pow 3 hL).neg.smul (hv 1)).mono (by simp)).sub (((hZ.pow 4 hL).smul (hv 2)).mono (by push_cast; linarith only [hu'])) hL|>.sub (((hZ.pow 3 hL).smul he).mono (by simp)) hL).congr (hs.mono fun i hi=> Eq.symm (Beyond _ hi (W' i) _)) -- whisk
end YM.OPE.Hark
