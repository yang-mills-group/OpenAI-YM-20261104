import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Curia
/-!
# Also in the true physical estimates: pay for a moment on a compact at one length

Only need polynomial-log bound in G.6 (later use tighter Leading limit, not claimed here).
Can do with raw physical prices `SingleLog` alone: insert far=vacant, through root with
weight 0 scalar terms. Done independently of upgrading the difference estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hG:G.Simple) (Z:PhysMS.tower S)
    {I J : Type}[Fintype I] {d:I→ℕ}{M δ:ℝ} (mn:0≤M)(dp:0<δ)
    {l:Filter J}{r:J→ℝ}{x:J→ I→E4}{o:J→E4}
    (H:SingleLog F Q.port) (u:Labels S d) (hr:Tendsto r l (𝓝[>] 0))
    (hx:∀ᶠ i in l, WithinRoom (r i) M δ (x i) (o i))
local notation "charge" k:max => fun i:J=> r i^k/r i^(∑ i,d i)
local notation "phase" i:max => spectator F i
private lemma ray (i:Viewers F) (x:I→E4) (p:I→C.book.Token) (h:Injective x) :
    observe (phase i) (beside x (Fin.elim0:Fin 0→E4)) (beside p (Fin.elim0:Fin 0→C.book.Token))=observe (phase i) x p := by
  let e:=Equiv.sumEmpty I (Fin 0); unfold beside
  rw [show Sum.elim x (Fin.elim0:Fin 0→E4)=x ∘ e from funext fun i=>by cases i; rfl; exact Fin.elim0 ‹Fin 0›,
    show Sum.elim p (Fin.elim0:Fin 0→C.book.Token)=p ∘ e from funext fun i=>by cases i; rfl; exact Fin.elim0 ‹Fin 0›]
  exact perm_observe _ (spectate F i).laws.toSymmetric e p h

include hr hx H mn dp Z hG
lemma compact_pay (p:J→Viewers F) : Allowance l r (charge 0) (fun i=> moment (phase(p i)) (x i) u) := by
  let Y: Fin 0→E4 := Fin.elim0; let t:Fin 0→C.book.Token:=Fin.elim0
  have hu (i:J): ClearOf (o i) Y 1 := ⟨fun j=>Fin.elim0 j,fun j=>Fin.elim0 j⟩
  obtain ⟨k,V⟩:= H.horizons I (Fin 0) (Orbits.names u) t δ M 1 dp mn zero_lt_one 0
  have H' := ((hr.eventually V).and hx).mono fun i h=> h.1 _ _ _ h.2 (hu i)
  let E i:= Q.port.truncated (phase (p i)) 0 (x i) (Orbits.names u) (o i) Y t
  have he : Allowance l r (charge 1) (fun i=> moment (phase(p i)) (x i) u-E i) := by
    refine ⟨k,IsBigO.of_bound' ?_⟩; filter_upwards [H',hr.eventually self_mem_nhdsWithin, log_pays hr] with i ⟨a,b,c⟩ u' v
    unfold E; rw [Real.norm_of_nonneg (by change 0<r i at u'; positivity), Orbits.observed, ← ray F (p i) (x i) (Orbits.names u) (beside_distinct.mp a).1]
    exact (c.phaseBound (p i)).trans_eq (mul_comm ..)
  have qt : Allowance l r (charge 0) E := by
    unfold E Prescription.truncated; refine Allowance.sum hr _ _ fun j hj=>?_
    have tj : j.1=0 := Nat.eq_zero_of_le_zero ((full_bands ..).mp hj)
    let V:=Q.port.ope (I:=I) j
    change Allowance _ _ _ (fun i=> V (x i) (Orbits.names u) (o i)*test0 F (o i) Q.port j (p i))
    simp_rw [picked F Z hG _ Q.port j (by rw [tj]; norm_num)]
    exact (Allowance.mul (costs F Q mn dp H u hr hx j) (Allowance.fixed _)).extend (u:=charge 0) (Eventually.of_forall fun i=>by simp only [tj,mul_one])
  refine (Allowance.add hr (he.transport (IsBigO.of_bound' ?_)) qt).congr (Eventually.of_forall fun i=> sub_add_cancel ..)
  filter_upwards [hr.eventually self_mem_nhdsWithin, (tendsto_nhdsWithin_iff.mp hr).1.eventually_lt_const zero_lt_one] with i h b
  rw [norm_div,norm_div,pow_one,pow_zero,Real.norm_of_nonneg h.le,norm_one]; gcongr
end YM.OPE.Flash259HorizonFork
