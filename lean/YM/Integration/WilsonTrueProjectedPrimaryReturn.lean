import YM.Integration.WilsonTrueProjectedSchool

/-! The signed change of the measured field coefficient in one genuine
Wilson step, with the stable feed and the old forced contribution. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPrimaryReturn
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open PhysicalNext Repeat Legato Graces Roost
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport WilsonTrueProjectedDualHistory
open WilsonTrueProjectedColumnDescent
open scoped Classical Topology Matrix.Norms.Frobenius

variable {G:Gauge} (R:Run G) {d i m N p k:ℕ}
local notation "𝓒" => R.family
local notation "σ" => ((𝓒).labels.level d).coeffSize
local notation "Q" => store (𝓒) d p
local notation "P" => (𝓒).path.rep N p i
local notation "V" => value (C := 𝓒) d N p
local notation "π" => page (C := 𝓒) d p
local notation "X" => measuring (𝓒) d N p
local notation "S" => (𝓒).localSection d
local notation "κ" => safety (𝓒)
local notation "U" => transition (C := 𝓒) d N p i

private theorem nonneg {n:Side} {h:ℕ} {F:Frame G h} {o:Site n} {W:Rep G n}
    {A:Coefficient F n} {w B:ℝ} (paid:A.remBound o W w B):0 ≤ B := by
  obtain ⟨a,b,ha,hb,price,_⟩ := paid
  exact (add_nonneg ha hb).trans price

/-- Both normalized projections use the same original incoming coordinates.
The signed difference includes the feed from the old null field and the
full soft part re-emitted by the two actual errors on the original vacuum. -/
theorem original (π₀:ℕ → Layout G) (Γ:ℕ → Pace.Coin)
    (Ψ:∀ j,Rep G ((𝓒).side j p)) (course:Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    (start : m ≤ i) (hi : i < N) (hc : Opened (𝓒) d i p) {γ ε : ℝ} (small : ε ≤ 1)
    (gate:Gate (𝓒) d N p i γ ε) (F:Spaces R p) {E b spare:ℝ} (y:(𝓒).label d)
    (upper:Full R (N := N) (d := d) Ψ F (i+1) y E)
    (fresh:WilsonTrueProjectedDualHistory.Signed R (N := N) (d := d) Ψ F i b)
    (hard:HardReturn R (N := N) (d := d) Ψ i spare) :
    ∃ v, Full R (N := N) (d := d) Ψ F i v (decay (𝓒) i*E+(2+4*stock (𝓒) i)*b+spare) ∧
      (∃ (s:Q i) (M:ℝ), reads d N p i s M ∧ F i=ᶠ[𝓝 1] V i s ∧ X i v=π i s) ∧
      σ (X i y-X i v) ≤ decay (𝓒) i*E+2*b+spare ∧
      ∃ (h:Q (i+1)) (e z:Q i) (B u:ℝ) (feed:(𝓒).label d),
        Admitted R Ψ (i+1) h B ∧ Admitted R Ψ i e b ∧ Admitted R Ψ i z u ∧
        U (F (i+1))=F i+e.density 0 S (Ψ i) ∧
        U (account h (Ψ (i+1)))=z.density 0 S (Ψ i) ∧
        X i y-X i v=X i feed+π i (soft (beside e z)) := by
  obtain ⟨s,M,paid,near⟩ := WilsonTrueProjectedGermIncome.on_course R π₀ Γ Ψ course start hi hc gate F y upper fresh hard
  obtain ⟨q,h,r,B,rq,null,hB,limit,input⟩ := upper
  obtain ⟨e,eb,ex,ef⟩ := fresh
  obtain ⟨z,u,zu,zx,zf,charge⟩ := hard h B hB
  obtain ⟨fm,rm,next,feed,nn,pn,rf,diff,output⟩ := WilsonTrueProjectedDualAppointment.original
    R π₀ Γ Ψ course start hi hc gate y q h e z s (F (i+1)) (F i) rq null hB
    ⟨eb.1,eb.2,ex⟩ ⟨zu.1,zu.2,zx⟩ near paid (by rw [input]; abel) ef zf
  let fit := fitting d N p i R.makes hc hi.le
  let v := fit.symm (π i s)
  have coord:X i v=π i s := fit.apply_symm_apply _
  have dn:0 ≤ decay (𝓒) i := Real.rpow_nonneg (zero_le_one.trans (factor_positive (𝓒) i).le) _
  have total := mul_le_mul_of_nonneg_left limit dn
  have sn:0 ≤ stock (𝓒) i := zero_le_one.trans (stage (𝓒) i).columns_ge
  have rn := nonneg rq.2
  have un := nonneg zu.2
  have head:σ (π i (soft (beside e z))) ≤ 2*(b+u) := by
    obtain ⟨point,owners,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course start hi.le
    have quiet := (course.1.walk i start hi.le).view
    obtain ⟨good,fare,_,_⟩ := WilsonMeasuredOnlyHard.original (beside e z) P (Ψ i)
      point quiet owners S (𝓒).params 0 (κ i) (b+u) fm rm
    apply control_page R.makes hc hi.le (soft (beside e z)) ⟨good,fare⟩
    change σ (beside e z).x ≤ b+u
    rw [reckon]
    exact (Size.add _ e.x z.x).trans (add_le_add ex zx)
  have exactFeed:X i y-X i v=X i feed+π i (soft (beside e z)) := by rw [coord]; exact diff
  refine ⟨v,⟨next,beside e z,_,_,nn,pn,⟨fm,rm⟩,?_,output⟩,⟨s,M,paid,near,coord⟩,?_,
    ⟨h,e,z,B,u,feed,hB,eb,zu,ef,zf,exactFeed⟩⟩
  · change decay (𝓒) i*r+(1+4*stock (𝓒) i)*(b+u)+(b+u) ≤ _
    linarith only [total,charge]
  · have old:2*u ≤ decay (𝓒) i*B+spare := 
      (mul_le_mul_of_nonneg_right (show 2 ≤ 2+4*stock (𝓒) i by linarith) un).trans charge
    have stable:ε*r*decay (𝓒) i ≤ r*decay (𝓒) i := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right small rn) dn).trans_eq (by ring)
    rw [exactFeed]
    calc
      _ ≤ σ (X i feed)+σ (π i (soft (beside e z))) := Size.add _ _ _
      _ ≤ ε*r*decay (𝓒) i+2*(b+u) := add_le_add rf head
      _ ≤ _ := by nlinarith only [total,old,stable]

end YM.Integration.WilsonTrueProjectedPrimaryReturn
