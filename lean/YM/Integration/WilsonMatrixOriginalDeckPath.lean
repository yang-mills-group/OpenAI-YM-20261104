import YM.Integration.WilsonMatrixOriginalDeckCutoff

/-! Recover a whole forward length trajectory from finite Wilson measurements on one spatial test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPath
open Filter Set MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Extraction.Order Table Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalDeckCutoff WilsonMatrixOriginalDeckMixed
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Increasing indices denote later target lengths. A step acts on the left. -/
def steps {X:Type*} [Monoid X] (v:ℕ→X) : ℕ→X
  | 0 => 1
  | n+1 => v n * steps v n

/-- The product uses the complete finite field space at every intermediate radius. -/
theorem composed (r:ℕ→ℝ) (n:ℕ) :
    steps (fun i=>change B J h (r (i+1)) (r i)) n=change B J h (r n) (r 0) := by
  induction n with
  | zero => exact (identity R B J h (r 0)).symm
  | succ n ih =>
    exact (congrArg (fun x=>change B J h (r (n+1)) (r n)*x) ih).trans
      (WilsonMatrixOriginalDeckReturn.compose R B J h (r (n+1)) (r n) (r 0))

/-- The genuine finite two-radius experiment at the later length. Both matrices use the same lattice. -/
def measured (g:Test 2) (r:ℕ→ℝ) (positive:∀ i,0<r i) (z:ℕ×ℕ) (i:ℕ) :=
  (raw R B J h g (positive (i+1)) (r (i+1)) z)⁻¹ * raw R B J h g (positive (i+1)) (r i) z

private theorem product_limit {X I:Type*} [Monoid X] [TopologicalSpace X] [ContinuousMul X]
    (u:Filter I) (x:I→ℕ→X) (y:ℕ→X) (n:ℕ) (each:∀i<n,Tendsto (fun z=>x z i) u (𝓝 (y i))) :
    Tendsto (fun z=>steps (x z) n) u (𝓝 (steps y n)) := by
  induction n with
  | zero => exact tendsto_const_nhds
  | succ n ih =>
    exact (each n (Nat.lt_succ_self n)).mul
      (ih (fun i hi=>each i (Nat.lt_trans hi (Nat.lt_succ_self n))))

/-- A single unit-mass localized test and one inverse bound work on the entire finite length path.
The finite cutoff and period are common to every step and every column of its product. -/
theorem original (L:PhysMS.Leading F J) (M:MS_Data G O) {p:E4} (hp:(0:E4)≠p)
    (U:Set (Points 2)) (near:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (C:ℝ) (V:Set ℝ), 0<C ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      V∈Trace.Pilot.trail ∧ ∀ (r:ℕ→ℝ) (positive:∀i,0<r i) (n:ℕ), (∀i≤n,r i∈V) →
        ∀ (u:Filter (ℕ×ℕ)) [u.NeBot], u≤f.fuse →
          (∀ᶠ z in u,∀i:Fin (n+1),IsUnit (raw R B J h g (positive i) (r i) z) ∧ ∀v:Glyph B h→ℂ,
            (∑a,‖v a‖)≤C*(∑a,‖(raw R B J h g (positive i) (r i) z *ᵥ v) a‖)) ∧
          Tendsto (fun z=>steps (measured R B J h g r positive z) n) u (𝓝 (change B J h (r n) (r 0))) := by
  obtain ⟨g,C,pos,supp,real,point,mass,all,window⟩ := WilsonMatrixOriginalDeckCutoff.original R B F J h L M hp U near
  obtain ⟨V,inside,active⟩ := Filter.Eventually.exists_mem window
  refine ⟨g,C,V,pos,supp,real,point,mass,all,inside,?_⟩
  intro r positive n dates u _ period
  refine ⟨Filter.eventually_all.mpr (fun i=>
    (active (r i) (dates i (by omega)) (positive i) u period).1),?_⟩
  rw [←composed R B J h r n]
  apply product_limit
  intro i hi
  exact (active (r (i+1)) (dates (i+1) (by omega)) (positive (i+1)) u period).2 (r i)

end YM.Integration.WilsonMatrixOriginalDeckPath
