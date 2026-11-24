import YM.OPE.Compatible.Docks.Sco
/-!
# Linear assembly across Fr basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open scoped Topology BigOperators Classical ContDiff
open Flume Flume.Page Flume.Script Silt.Float Silt
open Spells Drift Stroke
variable {I F E J:Type}{G:Gauge}{k d:ℕ}{f:Filter I}{v:I→ℝ}
-- sum pairing checkout
section
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars true in
lemma Asteroid {I E J : Type} {f : Filter I}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Type} [Fintype J] [DecidableEq J] (Q : K → (J → ℂ) →L[ℂ] ℂ)
    (y : I → J → E × E) (p : K → I → E →L[ℝ] ℝ)
    (hx : ∀ i w, Tendsto (fun j => p w j (y j i).1) f (𝓝 ((Q w (Pi.single i 1)).re)))
    (hy : ∀ i w, Tendsto (fun j => p w j (y j i).2) f (𝓝 ((Q w (Pi.single i 1)).im)))
    (s:K)(x:(J→ℂ)) : Tendsto (fun i=> doublet (p s i) (Arco (y i) x)) f (𝓝 ((Q s x).re,(Q s x).im)):=by
      have hp (j:J):Tendsto (fun i=> doublet (p s i) (y i j)) f (𝓝 ((Q s (Pi.single j 1)).re,(Q s (Pi.single j 1)).im)):= (hx j s).prodMk_nhds (hy j s); let H:=Q s; let B:=fun j:J=> ((H (Pi.single j 1)).re,(H (Pi.single j 1)).im); simp_rw[strums]; apply (show Tendsto (fun i=> Arco (fun j=> doublet (p s i) (y i j)) x) f (𝓝 (Arco B x)) from timers _ _ hp x)|>.mono_right; rw [show Arco B x=_ from FieldSum H x]
variable [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {K:Type}[Fintype J][DecidableEq J](Q:K→(J→ℂ)→L[ℂ]ℂ)
variable (y:I→ J → E × E)(p:K → I → E→L[ℝ] ℝ)
variable (hx:∀ i w,Tendsto (fun j=>p w j (y j i).1) f (𝓝 ((Q w (Pi.single i 1)).re)))
variable (hy:∀ i w,Tendsto (fun j=>p w j (y j i).2) f (𝓝 ((Q w (Pi.single i 1)).im)))
include hx hy
lemma Loans (hq:∀ x:(J→ℂ),(∀ j,Q j x=0)→ x=0) (η:I→ℝ)(h:Tendsto η f atTop)(hr:∀ j, Wax η f (p j) 0)(ht:Nonempty ((J→ℂ) ≃ₗ[ℝ] (E×E))) :
    ∃ U:I → (E×E)→L[ℝ] (J→ℂ), Wax η f U 0 ∧∀ᶠ i in f,U i ∘L Arco (y i)=ContinuousLinearMap.id ..∧ Arco (y i) ∘L U i= ContinuousLinearMap.id ..:=by
        let c:= (J→ℂ); let l(j:K×Bool)(i:I):= doublet (p j.1 i); let z(j:K×Bool): (J→ℂ)→L[ℝ] ℝ×ℝ:= ((Complex.reCLM).prod Complex.imCLM).comp ((Q j.1).restrictScalars ℝ); let a(i:K×Bool):ℝ×ℝ→L[ℝ]ℝ:= if i.2 then ContinuousLinearMap.fst .. else ContinuousLinearMap.snd ..; refine rayCou h (fun j i=> a j ∘L l j i) _ (fun j=>a j ∘L z j) ?_ ?_ ?_ ht
        · intro j; have hxΩ:Wax η f (l j) 0:= twins (hr j.1); exact zero_add (0:ℝ) ▸ RateLE.bil (RateLE.const (a j) (carth h)) hxΩ (Eventually.of_forall fun i=> ContinuousLinearMap.opNorm_comp_le (a j) (l j i))
        · intro x hp; refine hq x (fun v=> Complex.ext ?_ ?_); · exact hp (v,true)
          exact hp (v,false)
        intro x i
        have hp:Tendsto (fun i'=> l i i' (Arco (y i') x)) f (𝓝 (z i x)):= Asteroid Q y p hx hy i.1 x; exact ((a i).continuous.tendsto (z i x)).comp hp
end
end YM.OPE.Yolk
