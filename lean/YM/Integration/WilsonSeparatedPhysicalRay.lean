import YM.Integration.WilsonSeparatedContinuumGradients

/-! The actual full two-length physical product on one coordinate line.
Every derivative in the interpolation jet is differentiated on the same
genuine separated neighbourhood; the actual outer glyph stays at its own scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalRay
open Filter Function Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert Pert.Position RG17 Extraction Table Climb
open MS MS.Land MS.Menus MS.Local.Physical OPE.Nesting OPE.Levy Next.UVStress
open Frontier6.Road PhysicalNext.Repeat.Legato WilsonLimitConstruction
open WilsonSeparatedMovingRichGeometry WilsonSeparatedMovingRichVacuum WilsonSeparatedSpatialDescendant
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book} {n:ℕ}

open WilsonSeparatedContinuumGradients

private theorem continuousAction (E:Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]: ContinuousSMul ℝ E:=inferInstance
local instance (n:ℕ):ContinuousSMul ℝ (Points n):=continuousAction _

def axisStep (X:Points n) (i:Fin n) (a:Axis) (δ t:ℝ) : Points n := X+t • (δ • Points.direction i a)

def jet (i:Fin n) (a:Axis) (X:Points n) (δ:ℝ) (field:Points n→ℂ) (j:ℕ) (t:ℝ) : ℂ :=
  (δ^j) • derivatives (List.replicate j (i,a)) field (axisStep X i a δ t)

private lemma vicinity (r:ℝ) (y:Fin 1→E4) {X:Points n} (live:Injective (beside (posed r X) y)) :
    ∀ᶠ z in 𝓝 X,Injective (beside (posed r z) y) := by
  have sensor (i:Fin n⊕Fin 1):ContinuousAt (fun z:Points n=>beside (posed r z) y i) X := by
    cases i with
    | inl i=>change ContinuousAt (fun z:Points n=>r • z i) X;fun_prop
    | inr i=>exact continuousAt_const
  have pair (i j:Fin n⊕Fin 1):∀ᶠ z in 𝓝 X,i≠j→beside (posed r z) y i≠beside (posed r z) y j := by
    by_cases h:i=j
    · exact Eventually.of_forall fun _ ne=>False.elim (ne h)
    have sep:beside (posed r X) y i-beside (posed r X) y j≠0 := sub_ne_zero.mpr (fun eq=>h (live eq))
    exact (((sensor i).sub (sensor j)).tendsto.eventually_ne sep).mono fun _ ne _=>sub_ne_zero.mp ne
  filter_upwards [Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (pair i))] with z paid i j eq
  exact by_contra fun ne=>paid i j ne eq

private lemma last (w:Word n) (i:Fin n) (a:Axis) (f:Points n→ℂ) :
    derivatives (w++[(i,a)]) f = Points.gradient i a (derivatives w f) := by
  induction w generalizing f with
  | nil=>rfl
  | cons l w ih=>exact ih _

theorem smooth (F:Spec.Final R.family f V) (J:ℝ→tower V) (r:ℝ) (l:Word n) {d:Caps n}
    (v:(i:Fin n)→Free R.family (d i)) (y:Fin 1→E4) {e:Fin 1→ℕ} (w:Labels V e) {X:Points n}
    (live:Injective (beside (RG17.posed r X) y)) :
    DifferentiableAt ℝ (derivatives l (experiment J r v y w)) X := by
  let v':=labels F J r l d v
  have real: DifferentiableAt ℝ (experiment J r v' y w) X :=
    WilsonMacroscopicRelativeGradient.smooth F none (fun j=>(⟨grades l d j,J r (grades l d j) (v' j)⟩:V.Tag)) (fun j=>(⟨e j,w j⟩:V.Tag)) r y live
  have germ: derivatives l (experiment J r v y w) =ᶠ[𝓝 X] experiment J r v' y w :=
    (vicinity r y live).mono fun z ok=>marked F J r l d v y w z ok
  exact real.congr_of_eventuallyEq germ

private theorem translated {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x v:E) (t:ℝ) :
    HasDerivAt (fun y:ℝ=>x+y • v) v t := by
  simpa using (ContinuousLinearMap.toSpanSingleton ℝ v).hasDerivAt (x:=t) |>.const_add x

private theorem travel (i:Fin n) (a:Axis) (X:Points n) (δ t:ℝ) :
    HasDerivAt (axisStep X i a δ) (δ • Points.direction i a) t :=
  translated X (δ • Points.direction i a) t

private theorem lineSlope (p:Points n→ℂ) (i:Fin n) (a:Axis) (X:Points n) (δ t:ℝ)
    (smooth:DifferentiableAt ℝ p (axisStep X i a δ t)) :
    HasDerivAt (p ∘ axisStep X i a δ) (δ • Points.gradient i a p (axisStep X i a δ t)) t := by
  change HasDerivAt _ (δ • fderiv ℝ p _ (Points.direction i a)) t
  rw [←map_smul]
  exact smooth.hasFDerivAt.comp_hasDerivAt t (travel i a X δ t)

private theorem scalar (field:Points n→ℂ) (i:Fin n) (a:Axis) (X:Points n) (δ t:ℝ) (k:ℕ)
    (regular:DifferentiableAt ℝ (derivatives (List.replicate k (i,a)) field) (axisStep X i a δ t)) :
    HasDerivAt (jet i a X δ field k) (jet i a X δ field (k+1) t) t := by
  let p:=derivatives (List.replicate k (i,a)) field
  have convert:derivatives (List.replicate (k+1) (i,a)) field=Points.gradient i a p := by
    rw [List.replicate_succ',last]
  have first:=lineSlope p i a X δ t regular
  change HasDerivAt (fun t=>δ^k • p (axisStep X i a δ t)) (δ^(k+1) • derivatives _ field _) t
  rw [convert,pow_succ,←smul_smul]
  exact first.const_smul (δ^k)

theorem differentiate (F:Spec.Final R.family f V) (J:ℝ→tower V) (i:Fin n) (a:Axis) (X:Points n) (δ r:ℝ)
    {d:Caps n} (v:(i:Fin n)→Free R.family (d i)) (y:Fin 1→E4) {e:Fin 1→ℕ} (w:Labels V e) (k:ℕ) (t:ℝ)
    (safe:Injective (beside (RG17.posed r (axisStep X i a δ t)) y)) :
    HasDerivAt (jet i a X δ (experiment J r v y w) k)
      (jet i a X δ (experiment J r v y w) (k+1) t) t := by
  exact scalar _ i a X δ t k (smooth F J r (List.replicate k (i,a)) v y w safe)

end YM.Integration.WilsonSeparatedPhysicalRay
