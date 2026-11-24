import YM.Integration.WilsonPointChildProgram
import YM.Integration.WilsonMarkedIndependentPhysicalIntake

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildWinding
open Function Filter Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildProgram
open scoped BigOperators Classical Topology
open private tested from YM.Integration.WilsonDepositedRegisteredWinding
variable {G:Gauge}{ι:Type}[DecidableEq ι][Fintype ι]{D k:ι→ℕ}{e a m:ℕ}

/-- The actual Wilson step for the chosen residue, with its unaveraged
engineering weight. No incidence or finite scalar angular rank is screened. -/
theorem submitted (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(K:ι→ℕ)(S:Finset ι)
    (ha:a ≤ e)(r:ℕ){s:ℝ}(hs:0<s):
    ∃d:ℕ,∃C σ:ℝ,0 ≤ C ∧ 0<σ ∧ ∀N,m < N→∀(n:Side)(Y:Outerm G D),Wellness k Y→
    ∀V A:ℝ,1 ≤ V→1 ≤ A→PositiveAt Q.draws Q.paid e N (m+1) (n*(loose Q.draws m).L) s V→
    PairedAt e Y (n*(loose Q.draws m).L) s A→∀p:ι → Cover,
    let row:=next Q.draws Q.paid N m K k Y p S
    MarkU p S (row.1 n a r) (row.2 a r) σ (engineering (loose Q.draws m) K S*C*V^d*A^S.card):=by
  obtain ⟨F,hF,quiet⟩:=WilsonMarkedIndependentPhysicalIntake.prepare Q hm hs
  obtain ⟨W,hW,reset⟩:=WilsonFiniteVacuumWindingReset.rim Q hm ha r
  obtain ⟨d,C,σ,hC,hσ,step⟩:=WilsonFiniteIncomingMarkedWinding.original
    (D:=D) (k:=k) (r:=r) Q hm (subset_univ S) ha hs
  let P:=loose Q.draws m
  let c:=C*F^d*W
  have hc:0 ≤ c:=by dsimp [c]; positivity
  have small:(holt Q m hm s hs).s ≤ s:=by
    have hh:(holt Q m hm s hs).s ≤ s/32:=min_le_left ..
    linarith
  refine ⟨d,c,σ,hc,hσ,?_⟩
  intro N cut n Y well V A hV hA prior marked p row
  let cell:=inflate P S 0
  let x:=chartIn P p cell
  have read:=step N cut n (Y x) p cell (well.quiet' x) (well.level' x) (F*V) A
    (one_le_mul_of_one_le_of_one_le hF hV) (zero_le_one.trans hA) (quiet N cut n V hV prior)
    (fun T sub i hi l=>(marked x T i hi l).mono small)
  have wr:=mul_le_mul_of_nonneg_left (reset N cut)
    (show 0 ≤ C*(F*V)^d*A^S.card by positivity)
  have fee:=wr.trans_eq (show C*(F*V)^d*A^S.card*W=c*V^d*A^S.card by dsimp [c];rw [mul_pow];ring)
  have entered:=read.more fee
  let scale:=engineering P K S
  have nonneg:0 ≤ scale:=Finset.prod_nonneg fun v _=>pow_nonneg (Nat.cast_nonneg _) (K v)
  let pay:=scale • mend P cell D S
  have om:‖pay‖ ≤ scale:=by
    apply (ContinuousLinearMap.opNorm_smul_le scale (mend P cell D S)).trans
    rw [Real.norm_eq_abs,abs_of_nonneg nonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (mend_norm P cell D S) nonneg
  rw [show engineering P K S*c*V^d*A^S.card=scale*(c*V^d*A^S.card) by dsimp [scale];ring]
  convert tested pay om entered using 1 <;> funext t <;> rfl

end YM.Integration.WilsonPointChildWinding
end
