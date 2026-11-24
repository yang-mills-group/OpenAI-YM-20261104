import YM.Integration.OriginalMarkedRootDependence
import YM.Integration.OriginalFiniteRootPlacement
import YM.WilsonCoeffUV.Horizon.OrbitShift

/-! Changing the presentation anchor on a thin physical cluster changes
its marked lifts by one common lattice period. Original translation
covariance therefore identifies the two retained periodized cover rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedLiftAgreement
open Function Finset Wilson Lattice RG Marker Gauge Precision FreeResolvent
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Work.F08
open OriginalMarkedRootDependence
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {D : V→ℕ}

private theorem component (a b : Site n) (i : Axis) :
    |lift (a-b) i| ≤ (separation a b:ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast (le_sup (f:=fun j : Axis => (lift (a-b) j).natAbs) (mem_univ i))

omit [DecidableEq V] [Fintype V] in
theorem common (J : Finset V) (p : V→Site n) (v w : V) (hv : v∈J) (hw : w∈J)
    {size : ℕ} (hsize : ∀a∈J,∀b∈J,separation (p a) (p b) ≤ size) (thin : 4*size < n.val) :
    ∃ t : Cover, wrap n t=0 ∧ ∀ a∈J,
      PeriodicMarkedWinding.roots n p w a=t+PeriodicMarkedWinding.roots n p v a := by
  let δ := fun a => lift (p a-p v)
  let t := lift (p w)-lift (p v)-δ w
  refine ⟨t,by simp [t,δ],?_⟩
  intro a ha
  have exactDiff : lift (p a-p w) = δ a-δ w := by
    apply lift_eq_iff.mpr
    refine ⟨by simp [δ],?_⟩
    intro i
    have lim (b : V) (hb : b∈J) : -(size:ℤ)≤δ b i ∧ δ b i≤(size:ℤ) :=
      abs_le.mp ((component (p b) (p v) i).trans (by exact_mod_cast hsize b hb v hv))
    have h₁ := lim a ha
    have h₂ := lim w hw
    have h₃ : 4*(size:ℤ)<(n.val:ℤ) := by exact_mod_cast thin
    dsimp only [Pi.sub_apply]
    omega
  change lift (p w)+lift (p a-p w) = t+(lift (p v)+δ a)
  rw [exactDiff]
  dsimp only [t]
  abel

omit [DecidableEq V] [Fintype V] in
theorem collapse {J : Finset V} (P : Era G (Pen D J)) (t : Cover) (ht : wrap n t=0) (i l : ℕ) :
    Carp.plume ((shifted P t).2 i l) n=Carp.plume (P.2 i l) n := by
  change Carp.plume (revolve t (P.2 i l)) n=_
  rw [sigmaMint,ht]
  funext z
  simp [revolve,jog]

omit [Fintype V] in
/-- A general original marked family can already contain every joint
submask. Its original Wellness and common translation law are used on
exactly that family, in the original native spatial block. -/
theorem thinCover (A : Levels G) (O : ChartRatio G) {m N : ℕ} (hN : m<N)
    (hG : G.Simple) (hO : LocalRatio O) (M : Outerm G D) (k : V→ℕ)
    (well : Wellness k M) (shift : ∀u,ramble u M) (n : Side) (J : Finset V)
    (p : V→Site n) (v w : V) (hv : v∈J) (hw : w∈J) (cells : V→Site (loose A m).L)
    {size : ℕ} (span : ∀a∈J,∀b∈J,separation (p a) (p b) ≤ size) (tiny : 4*size < n.val) (i l : ℕ) :
    let next := fun y => logO A O m N (M (chartIn (loose A m) y cells)) k J
    Carp.plume ((next (PeriodicMarkedWinding.roots n p w)).2 i l) n =
      Carp.plume ((next (PeriodicMarkedWinding.roots n p v)).2 i l) n := by
  let y := PeriodicMarkedWinding.roots n p v
  let z := PeriodicMarkedWinding.roots n p w
  let P := loose A m
  let Y := chartIn P y cells
  let Z := chartIn P z cells
  obtain ⟨t,ht,loc⟩ := common J p v w hv hw span tiny
  let T := (A.S.block m).val • t
  have hx (j : V) (hj : j∈J) : Z j=T+Y j := by
    change P.L.val • z j + lift (cells j)=P.L.val • t+(P.L.val • y j + lift (cells j))
    have location : z j=t+y j := loc j hj
    rw [location,nsmul_add,add_assoc]
  have reg : OriginalMarkedRootDependence.«scoped» M := fun s p q h => well.filial p q s h
  have he := transfer_scoped M reg A O m N k J Z (steppedC T Y) hx
  have move := congrFun (alongShift well hN hG hO (shift T) Y (u:=t)) J
  change Carp.plume ((logO A O m N (M Z) k J).2 i l) n =
    Carp.plume ((logO A O m N (M Y) k J).2 i l) n
  change logO A O m N (M Z) k J=logO A O m N (M (steppedC T Y)) k J at he
  change logO A O m N (M (steppedC T Y)) k J=raised0 t (logO A O m N (M Y) k) J at move
  rw [he,move]
  exact collapse (logO A O m N (M Y) k J) t ht i l

end YM.Integration.OriginalMarkedLiftAgreement
end
