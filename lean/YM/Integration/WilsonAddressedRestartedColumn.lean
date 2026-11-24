import YM.Integration.WilsonOriginalMicroscopicGuardedReporters
import YM.Integration.WilsonCapturedBookedFlow

/-! The original guarded trial and its matched Wilson cutoff column, at one
aligned reporter. The signed cutoff difference is retained on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedRestartedColumn
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonCapturedFactoryCocycle WilsonOriginalMicroscopicGuardedReporters
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d N p : ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d

def track (K : ℕ) (F : Config G ((C₀).side K p) → ℂ) : Er C₀ p :=
  fun i => if h : i ≤ K then Nat.decreasingInduction
    (motive := fun a _ => Config G ((C₀).side a p) → ℂ)
    (fun j _ => transition (C:=C₀) d N p j) F h else 0

theorem at_top (K : ℕ) (F : Config G ((C₀).side K p) → ℂ) :
    track R d N p K F K = F := by
  unfold track
  rw [dif_pos le_rfl, Nat.decreasingInduction_self]

theorem step {i K : ℕ} (h : i<K) (F : Config G ((C₀).side K p) → ℂ) :
    track R d N p K F i = transition (C:=C₀) d N p i (track R d N p K F (i+1)) := by
  unfold track
  rw [dif_pos h.le, dif_pos (show i+1≤K from h), Nat.decreasingInduction_succ_left _ _ h h.le]

theorem segment {K i : ℕ} (F : Config G ((C₀).side K p) → ℂ) (n : ℕ) (h : i+n≤K) :
    track R d N p K F i = flow C₀ d N p i n (track R d N p K F (i+n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      _ = flow C₀ d N p i n (track R d N p K F (i+n)) := ih (by omega)
      _ = _ := congrArg (flow C₀ d N p i n) (step R d N p (by omega : i+n<K) F)

theorem original (simple : G.Simple) : ∀ᶠ j : ℕ in atTop,
    ∀ N p K (before : j≤K) (high : K≤N) (target : ℕ) (η : ℝ)
      (A : (C₀).label d ≃ₗ[ℂ] (C₀).label d) (x : (C₀).label d),
    let e := page (C:=C₀) d p j (((C₀).factory d N p).entries j x)
    let w := A.symm e
    let F := numerator R d N p K 0 w
    let B := (1+4*stock C₀ K)*(F₀).coeffSize w
    Arrived R d j K N p target before high η A e →
    ∀ f, j≤f → f≤K → ∃ q : store C₀ d p f, ∃ y : (C₀).label d,
      reads (C:=C₀) d N p f q (hike C₀ K f rate*B) ∧
      page (C:=C₀) d p f q=0 ∧ mCost C₀ d N p f y ≤ 2*hike C₀ K f rate*B ∧
      track R d N p K F f - calValues (C:=C₀) d N p f x =
        value (C:=C₀) d N p f q + calValues (C:=C₀) d N p f y := by
  obtain ⟨j₀,opened⟩ := eventually_atTop.mp (open_late C₀ simple d)
  obtain ⟨_,_,returning⟩ := WilsonCapturedReturnedCrossing.purchased R d simple (γ:=rate/2) (ε:=1)
    (by norm_num [rate]) (by norm_num [rate]) zero_lt_one le_rfl
  filter_upwards [returning,eventually_ge_atTop j₀] with j stable room
  intro N p K before high target η A x e w F B arrival f jf fK
  have jN := before.trans high
  obtain ⟨_,q,format,paid,field,measured,_⟩ := arrival
  have same : ((C₀).path.rep N p j).p=(C₀).path.levels.budget j := (R.makes.wilson.represents N p j jN).vac
  have measured' : page (C:=C₀) d p j q=e := by
    change projection F₀ (C₀).params ((C₀).path.rep N p j).p.threshold 0 q=e at measured
    rw [same] at measured
    exact measured
  obtain ⟨z,_,unique,_,award⟩ := stable p N jN q ⟨format,paid⟩
  have zx : x=z := unique x measured'.symm
  subst z
  let raw := track R d N p K F
  have birth : raw K=value (C:=C₀) d N p K (primary 0 w) := at_top R d N p K F
  have receive : raw j=value (C:=C₀) d N p j q := by
    rw [show value (C:=C₀) d N p j q=_ from field]
    change raw j = flow C₀ d N p j (K-j) _
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le before
    rw [Nat.add_sub_cancel_left]
    exact (segment R d N p F n le_rfl).trans (congrArg (flow C₀ d N p j n) (at_top R d N p (j+n) F))
  have prior : reads (C:=C₀) d N p K (primary 0 w) ((F₀).coeffSize w) :=
    ⟨primary_format w,rem_mono (primary_rem w (Real.sqrt_pos.mpr (Real.exp_pos _))) (Work.G08.size_nonneg F₀ w)⟩
  have moves (i : ℕ) (ji : j ≤ i) (iK : i < K) :
      Foreground C₀ d N p i ((0 : Er C₀ p) i) 0 ∧
      raw i=transition (C:=C₀) d N p i (raw (i+1)) + (0 : Er C₀ p) i := by
    exact ⟨(WilsonCapturedBookedFlow.retained R d N p 0 continuous_zero high
      (fun l jl => opened l (room.trans jl) p) i ji iK).1, (step R d N p iK F).trans (add_zero _).symm⟩
  obtain ⟨Q,Y,result⟩ := award before high (primary 0 w) prior le_rfl (by rfl : 0≤(0:ℝ)) receive birth moves
  obtain ⟨shot,price⟩ := result f jf fK
  refine ⟨Q f,Y f,?_,shot.zero,?_,shot.detailed⟩
  · simpa only [mul_zero,add_zero] using shot.ready
  · simpa only [mul_zero,zero_add,mul_one] using price

end YM.Integration.WilsonAddressedRestartedColumn
end
