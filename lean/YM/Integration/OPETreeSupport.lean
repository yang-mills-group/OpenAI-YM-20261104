import YM.Integration.OPETreeKernel
import YM.Integration.OPETreeCompact

/-! The independent MS multipoint tree OPE on an arbitrary compact
subset of the separated inner configuration space. All inner shapes
share the radius window and constant for each fixed exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OPETreeSupport
open Function Set Filter Asymptotics Maxwell Maxwell.Free Maxwell.Wick
open FVA2 Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood MSbar.OPE
open OPETreeRemainder OPETreeKernel OPETreeCompact
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {n m i d : ℕ}

def room (y : Tail m) : Set (ℝ × Points n) :=
  {a | a.2 ∈ conf n ∧ foreign (inside a.2 a.1 y.c) y.y}

theorem room_open (y : Tail m) : IsOpen (room (n := n) y) := by
  apply IsOpen.inter ((conf_open n).preimage continuous_snd)
  change IsOpen {a : ℝ × Points n | ∀ i j, y.c+a.1 • a.2 i ≠ y.y j}
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_ne.preimage (continuous_const.add (continuous_fst.smul (coordinate_smooth i).continuous))

theorem room_zero (y : Tail m) {x : Points n} (hx : x ∈ conf n) : (0,x) ∈ room y := by
  refine ⟨hx, fun i j => ?_⟩
  change y.c+(0:ℝ) • x i ≠ y.y j
  rw [zero_smul, add_zero]
  exact exterior_apart y (0 : Fin 1) j

def tested (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G)
    (k : ℕ) (x : Points n) : ℂ := coefficient (kernel y p q) k x

theorem tested_smooth (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G)
    (k : ℕ) {x : Points n} (hx : x ∈ conf n) : ContDiffAt ℝ ∞ (tested y p q k) x :=
  coefficient_smooth (at_zero y p q x hx) k

theorem kernel_bound (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n)
    (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G) (H : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ x ∈ K,
      (r,x) ∈ room y ∧
      ‖kernel y p q (r,x) - ∑ k ∈ Finset.range (H+1), (r:ℂ)^k * tested y p q k x‖ ≤ B*r^(H+1) := by
  have hh (a : ℝ × Points n) (ha : a ∈ room y) : ContDiffAt ℝ ∞ (kernel y p q) a :=
    smooth_at y p q a ha.1 ha.2
  unfold tested
  exact uniform_taylor (A := Points n) (U := room (n := n) y) (f := kernel y p q)
    (room_open (n := n) y) hh K hK (fun x hx => room_zero y (hsep hx)) H

variable (V : Warehouse G) {Q : MS.Land.Booked (FVA2.ColorCode.wings G)}
    (M : MS.Land.MS_Data G Q) (μ : ℝ) (v : Fin n → E V.F i) (w : Fin m → E V.F d)
    (weights : Fin n → ℕ) (hv : ∀ a, pureW scaleW (weights a) (polynomials V.F i v a))
include hv

/-- Testing the independent local Wick field at any exterior gives
the corresponding radial derivative of the jointly smooth kernel. -/
theorem coefficient_reads (x : conf n) (y : Tail m) (k : ℕ) :
    tested y (polynomials V.F i v) (polynomials V.F d w) k x.val =
      paired V M μ 0 (RG11.Neighborhood.close y) (fun _ : Fin 1 => output V.F x v k) w := by
  let p := polynomials V.F i v
  let q := polynomials V.F d w
  apply congrFun (OPETreeCompact.unique (fun r => kernel y p q (r,x.val))
    (fun l => tested y p q l x.val)
    (fun l => paired V M μ 0 (RG11.Neighborhood.close y) (fun _ : Fin 1 => output V.F x v l) w) ?_ ?_) k
  · intro H
    obtain ⟨B,_,hb⟩ := kernel_bound {x.val} isCompact_singleton
      (singleton_subset_iff.mpr x.property) y p q H
    apply IsBigO.of_bound B
    filter_upwards [hb,self_mem_nhdsWithin] with r hr hpos
    rw [Real.norm_of_nonneg (pow_nonneg (show 0 < r from hpos).le _)]
    exact (hr x.val (mem_singleton _)).2
  intro H
  apply (ray_remainder V M μ x y v w weights hv H).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin,
    (contracts (x := x.val) y.c y.y (exterior_apart y)).filter_mono nhdsWithin_le_nhds]
    with r hr hfar
  rw [normalized V M μ x y v w weights hv r hr hfar]

/-- The direct field remainder, simultaneous on every inner shape in
the compact support, with a full missing engineering degree. -/
theorem compact_remainder (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n)
    (y : Tail m) (H : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ x : conf n, x.val ∈ K →
      driven r x.val y ∈ conf (n+m) ∧
      ‖(r:ℂ)^(∑ a,weights a) * paired V M μ 0 (driven r x.val y) v w -
        ∑ k ∈ Finset.range (H+1), (r:ℂ)^k *
          paired V M μ 0 (RG11.Neighborhood.close y) (fun _ : Fin 1 => output V.F x v k) w‖ ≤ B*r^(H+1) := by
  obtain ⟨B,hB,h⟩ := kernel_bound K hK hsep y (polynomials V.F i v) (polynomials V.F d w) H
  refine ⟨B,hB,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r hr hp x hx
  obtain ⟨hs,hb⟩ := hr x.val hx
  refine ⟨combination (safe x.property y.c hp) (Points.tail_in y.apart) hs.2,?_⟩
  rw [normalized V M μ x y v w weights hv r hp hs.2]
  simpa only [coefficient_reads V M μ v w weights hv x y] using hb

end YM.Integration.OPETreeSupport
