import YangMills.WilsonProof.NativeSupport.JointMountFlags
import YangMills.WilsonProof.NativeSupport.JointSheetMaps
import YangMills.WilsonProof.NativeSupport.JointRootedInput

/-! Local primitive sources on an injectively dated part of the alphabet.
The fresh price contains its own amplitude. Color flags for a source at
birth cost no old-owner radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset MeasureTheory Lattice RG Wilson Marker MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories Push.GridApprox.Nil
open scoped Classical BigOperators
variable {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] {G:Gauge} {n:Side}
variable (R:Rep G n) (B:Census V) (birth:J → V) (X:J → Support n) (F:J → Config G n → ℂ)
variable (o:V → Site n) (home : ∀ i,o (birth i)∈X i) (loc:∀ i,LocalOn (X i) (F i))
variable (sym:∀ i,GaugeInvariant (F i)) (meas:∀ i,Measurable (F i))

include home loc sym meas in
omit [Fintype J] in
theorem fresh_borne (reg:Bool) (i:J) :
    Borne o (X i) (fresh R B birth X F reg i) R.p.threshold := by
  refine ⟨?_,?_,?_,?_⟩
  · intro U Z agree flags
    have al : Healthy R.p.threshold (X i) U ↔ Healthy R.p.threshold (X i) Z := by
      simp only [Healthy,disjoint_iff_inter_eq_empty,flags]
    simp only [fresh,al,loc i U Z agree]
  · intro k U
    have al : Healthy R.p.threshold (X i) (gauge k U) ↔ Healthy R.p.threshold (X i) U := by simp only [Healthy,gauge_flags]
    simp only [fresh,al,sym i k U]
  · intro p
    by_cases hit : p=B.fire (birth i)
    · simp only [fresh,Poly.part_send,if_pos hit]
      cases reg
      · convert (meas i).sub (masked_measurable R.p.threshold (X i) (F i) (meas i)) using 1
        funext U
        by_cases h : Healthy R.p.threshold (X i) U <;> simp [masked,h]
      · convert masked_measurable R.p.threshold (X i) (F i) (meas i) using 1
        funext U
        by_cases h : Healthy R.p.threshold (X i) U <;> simp [masked,h]
    · simp [fresh,Poly.part_send,hit]
  · intro U
    apply scope_send
    intro j member
    exact (mem_singleton.mp member).symm ▸ home i

include home in
theorem fresh_towed (inj : Injective birth) (w:V → ℝ) (hw:∀ v,0 < w v) (amp:J → ℝ) (pa:∀ j,0 ≤ amp j)
    (bound:∀ j U,‖F j U‖ ≤ amp j) {μ M:ℕ} (occ:Occupancy o μ) (e t:ℝ) (t0:0 ≤ t)
    (invoice:∀ j, Real.exp ((e+1)*coverNumber M (X j))*(w (birth j)*amp j) ≤ t) (reg:Bool) :
    Towed w X (fresh R B birth X F reg) M e (μ*siteFactor M*t) := by
  let cost i := w (birth i)*amp i
  have pc i : 0 ≤ cost i := mul_nonneg (hw _).le (pa _)
  have roots : Rooted (fun i:J=>{birth i}) X M (e+1) cost t := by
    intro v
    apply Budget.certify
    · intro j
      split
      · exact mul_nonneg (Real.exp_pos _).le (pc _)
      · rfl
    · intro D
      by_cases present : ∃ j∈D,birth j=v
      · obtain ⟨j,hj,hv⟩:=present
        rw [sum_eq_single j]
        · simpa [hv,cost] using invoice j
        · intro k _ different
          have ne : v ≠ birth k := by intro ka; exact different (inj (ka.symm.trans hv.symm))
          simp [ne]
        · intro bad
          exact False.elim (bad hj)
      · have zero : ∀ i∈D,v ≠ birth i := fun i hi eq=>present ⟨i,hi,eq.symm⟩
        rw [sum_eq_zero (fun i hi=>by simp [zero i hi])]
        exact t0
  refine ⟨cost,Summable.of_finite,root_hit occ pc t0 (fun i _=>⟨birth i,mem_singleton_self _,home i⟩) roots,?_⟩
  intro i
  unfold fresh
  simpa only [Poly.solo_toll,cost] using satin (w:=w) (fun U=>if Healthy R.p.threshold (X i) U ↔ reg=true then F i U else 0)
    (B.fire (birth i)) (amp i) (pa i) (fun U=>by split; exact bound i U; simpa using pa i)

end YM.Integration.InletSusceptibility.JointShadow
namespace YM.Integration.InletSusceptibility.Painted
open Function Finset Marker Packet
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V]

def active (fresh:Finset V) : Finset (Ink V) := univ.filter fun v=>v.2.1=true ∨ v.1∈fresh

def newborn (v:V) : Ink V := (v,false,false)

omit [Fintype V] in
theorem new_weight (w:V → ℝ) (A D:ℝ) (fresh:Finset V) (v:V) (hv:v∈fresh) :
    weight w A D fresh (newborn v)=w v*D := by simp [newborn,weight,hv]

theorem old_owns (fresh S:Finset V) (nonempty:S.Nonempty) : ∃ u∈wear S,u∈active fresh := by
  let k:=nonempty.choose
  let f:=paint k true false
  have hit : f k∈wear S := by
    rw [wear,dif_pos nonempty]
    exact mem_map.mpr ⟨k,nonempty.choose_spec,rfl⟩
  exact ⟨f k,hit,by simp [f,active,paint]⟩

theorem old_or_gain (fresh:Finset V) (S:Finset (Ink V)) (single : ¬gains fresh S) :
    Disjoint (S.image Prod.fst) fresh ∧ ((S∩active fresh).card ≤ 1) := by
  have none : ∀ x∈S,x.1∉fresh := by
    intro x hx born
    exact single (Or.inr (card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,born⟩⟩))
  have cut : S∩active fresh=S.filter (fun p=>p.2.1) := by
    ext x
    by_cases hx:x∈S
    · simp [active,hx,none x hx]
    · simp [hx]
  refine ⟨disjoint_left.mpr ?_,?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hv
    exact none x hx
  · rw [cut]
    have small:¬2 ≤ (S.filter (fun p=>p.2.1)).card := fun h=>single (Or.inl h)
    omega

end YM.Integration.InletSusceptibility.Painted
