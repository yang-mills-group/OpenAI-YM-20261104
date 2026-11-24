import YM.Integration.ManuscriptQLocalPacketDisplacement
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Polynomial.Eval.Degree
import YM.Integration.ManuscriptQLocalActualLog
import YM.Integration.ManuscriptQLocalEffectiveInput
import YM.Comparison.RG02.Valence.Amplify
import YM.Comparison.RG02.Assembly.Kernel
import YM.Comparison.RG02.Laplace.Trunc
import YM.Comparison.RG02.Integral.Bill
import YM.Comparison.RG02.Laplace.Fleet

/-! The original forest phase coefficients and their finite regulated Wilson reconstruction. -/
set_option autoImplicit false
noncomputable section

section
/-! The complete genuine cleared marked field of a joint RG02 input on an
original forest is determined by its independent finite unit-phase samples.
This identity precedes differentiation. It therefore recovers every mixed
derivative and its actual finite Wick-generator polynomial. -/
namespace YM.Integration.ManuscriptQLocalPhaseJets

open Filter Function Finset Lattice Wilson RG Marker Multi Exterior
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open Assembly Cumulants Tree MvPolynomial
open ManuscriptQLocalPacketGrades
open scoped BigOperators Classical Topology ContDiff

def interpolation {D : ℕ} (z : ℂ) (j : ZMod (D+1)) : ℂ :=
  ∑k : ZMod (D+1), z^k.val*ManuscriptQLocalSourceFourier.weight j k

theorem evaluate {D : ℕ} (p : Polynomial ℂ) (hp : p.natDegree≤D) (z : ℂ) :
    p.eval z = ∑j : ZMod (D+1),interpolation z j*p.eval (ManuscriptQLocalSourceFourier.phase j) := by
  have base : p.eval z = ∑k : ZMod (D+1),p.coeff k.val*z^k.val := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
    change _ = ∑k : Fin (D+1),p.coeff k.val*z^k.val
    exact (Fin.sum_univ_eq_sum_range (fun k:ℕ=>p.coeff k*z^k) (D+1)).symm
  rw [base]
  calc
    _ = ∑k : ZMod (D+1), ∑j : ZMod (D+1),z^k.val*
        ManuscriptQLocalSourceFourier.weight j k*p.eval (ManuscriptQLocalSourceFourier.phase j) := by
      apply sum_congr rfl
      intro k _
      rw [←ManuscriptQLocalSourceFourier.polynomial p hp k,ManuscriptQLocalSourceFourier.projection,
        Finset.sum_mul]
      apply sum_congr rfl
      intro j _
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [Finset.sum_comm]; simp only [interpolation,Finset.sum_mul]

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {G : Gauge}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
local notation "ph" => ManuscriptQLocalSourceFourier.phase
local notation "𝔽" => ZMod (F.packets.powerCap+1)

def field (Λ : Forest (S).ratio) (x : TestSpace J.tests) (s : Hot Γ) (z : ℂ) :=
  Bulk.markFn S Λ (ManuscriptQLocalEffectiveInput.colors F z x) s

theorem material (hg : g₀≠0) (Λ : Forest (S).ratio) (x : TestSpace J.tests) (s : Hot Γ)
    (z : ℂ) (y : Bulk.Joint S Λ (G:=G)) :
    field F Λ x s z y=∑ j : 𝔽, interpolation z j • field F Λ x s (ph j) y := by
  let U := Work.F03.live Λ y.2
  let P := ManuscriptQLocalPhaseMark.ink F.packets g₀ x y.1 U s.val
  have h (q : ℂ) := ManuscriptQLocalPhaseMark.measured F.input_paid hg x y.1 U q s.val
  let γ : ℝ := y.1^(NativePaidPacketColors.commonPower (phaseSource F.packets g₀ 1))
  have e (q : ℂ) : field F Λ x s q y=(γ:ℂ)*P.eval q := by
    change γ • ((phaseSource F.packets g₀ q).read x y.1 U).part s.val=_
    rw [←h q,Complex.real_smul]
  rw [e z,evaluate P (ManuscriptQLocalPhaseMark.degree _ _ _ _ _ _) z,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  rw [e (ph j),smul_eq_mul]
  ring

theorem mixed (hg : g₀≠0) (Λ : Forest (S).ratio) (x : TestSpace J.tests) (s : Hot Γ)
    (z : ℂ) (k : ℕ) :
    iteratedFDeriv ℝ k (field F Λ x s z) 0 =
      ∑j : 𝔽, interpolation z j • iteratedFDeriv ℝ k (field F Λ x s (ph j)) 0 := by
  have hs (j : 𝔽) : ContDiffAt ℝ k (field F Λ x s (ph j)) 0 :=
    (Bulk.joint_receipt S Λ
      ((ManuscriptQLocalEffectiveInput.convention F hg (ph j)
        (ManuscriptQLocalSourceFourier.unit j)).well x |>.suppose_mark s)).smooth.of_le le_top
  rw [show field F Λ x s z = fun y=>∑ j : 𝔽,interpolation z j •
    field F Λ x s (ph j) y from funext (material F hg Λ x s z),
    iteratedFDeriv_fun_sum_apply (fun j _=>(hs j).const_smul (interpolation z j))]
  apply sum_congr rfl
  intro j _
  change iteratedFDeriv ℝ k ((interpolation z j) • (field F Λ x s (ph j))) 0=_
  exact iteratedFDeriv_const_smul_apply (a:=interpolation z j) (hs j)

theorem radial (hg : g₀≠0) (Λ : Forest (S).ratio) (x : TestSpace J.tests) (s : Hot Γ)
    (z : ℂ) (k : ℕ) (v : Bulk.Joint S Λ (G:=G)) :
    Assembly.jet (field F Λ x s z) k v =
      ∑j : 𝔽,interpolation z j • Assembly.jet (field F Λ x s (ph j)) k v := by
  unfold Assembly.jet
  rw [mixed F hg Λ x s z k,_root_.sum_apply,Finset.smul_sum]
  apply sum_congr rfl
  intro j _
  rw [smul_apply,smul_comm]

/-- Equality of actual full finite polynomials, on every genuine input
forest and with every original spatial key held independent. -/
theorem kernel (hg : g₀≠0) (Λ : Forest (S).ratio) (x : TestSpace J.tests) (s : Hot Γ)
    (z : ℂ) (k : ℕ) {I : Type} [Fintype I] [DecidableEq I]
    (y : Bulk.Joint S Λ (G:=G)) (L : (I→ℝ)→ₗ[ℝ] Bulk.Joint S Λ (G:=G)) :
    Assembly.kernelJet y L (field F Λ x s z) k =
      ∑j : 𝔽,MvPolynomial.C (interpolation z j) *
        Assembly.kernelJet y L (field F Λ x s (ph j)) k := by
  apply Valence.Enlist.paint_inj
  intro v
  rw [map_sum,Assembly.reading,radial F hg]
  apply sum_congr rfl
  intro j _
  rw [map_mul,Assembly.reading]
  simp only [smul_eq_mul]
  congr 1
  simp [Cloud.paint]

end YM.Integration.ManuscriptQLocalPhaseJets
end

section
/-! Finite displacement grading on the original correlated Gaussian.
The auxiliary coupling slots have weight zero. Its complete vacuum
denominator is constant in the marking phase before the logarithm. -/
namespace YM.Integration.ManuscriptQLocalWickLedger

open MeasureTheory Finset Marker Multi Comparison.RG02
open Order Cumulants Next.Rank Next.SectorChange.Gaussian
open ManuscriptQLocalShiftLedger
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V} {r : ℕ}

def allocation (D : ℕ) : V ⊕ Fin r→ℕ := Sum.elim (fun _=>D) (fun _=>0)

omit [Fintype V] in
theorem constant_weight (D : ℕ) (s : Γ.Mode) :
    weight (fun _ : V=>D) s=s.val.card*D := by
  simp [weight]

theorem pair_weight (D : ℕ) (s : Γ.Mode) (q : Index r) :
    weight (allocation D) (Join.pair s q)=s.val.card*D := by
  simp [weight,allocation,Join.pair,Finset.sum_disjSum]

theorem board_weight (D : ℕ) (s : (Board Γ r).Mode) :
    weight (allocation D) s=(Join.left s).val.card*D := by
  calc
    _ = weight (allocation D) (Join.pair (Join.left s) (Join.right s)) :=
      congrArg _ (Join.pair_reunite s).symm
    _ = _ := pair_weight .. 

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Test every genuine repeated-coordinate Gaussian vertex polynomial on a
single common Gaussian variable. All spatial correlations survive. -/
theorem gaussian (D : ℕ) (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hq : Q.PosSemidef)
    (p : ℂ→Hot (Board Γ r)→Normal.poly I)
    (hp : ∀ (u : I→ℝ) (e : Hot (Board Γ r)),∃P : Polynomial ℂ,
      P.natDegree≤(Join.left e.val).val.card*D ∧
      ∀z,P.eval z=Cloud.paint u (p z e)) :
    Ledger (allocation D) (fun z=>Cloud.prescription Q hQ 0 (p z)) := by
  let X := fun z u=>Poly.pass (lit (Board Γ r) (fun e=>Cloud.paint u (p z e)))
  have point (u : I→ℝ) : Ledger (allocation D) (fun z=>X z u) := by
    apply Ledger.pass
    apply active
    intro e
    simpa only [board_weight] using hp u e
  have real (z : ℂ) (s : (Board Γ r).Mode) :
      Integrable (fun u=>(X z u).part s) (cloud Q) ∧
      (∫u,(X z u).part s ∂cloud Q)=(Cloud.prescription Q hQ 0 (p z)).part s := by
    simpa only [X,zero_add,Cloud.shift_zero] using
      Cloud.gaussian Q hQ hq (0:I→ℝ) (p z) s
  have hgood (z : ℂ) : Actual.Good (cloud Q) (X z) := fun s=>(real z s).1
  have hread : (fun z=>Actual.charge (cloud Q) (X z))=
      (fun z=>Cloud.prescription Q hQ 0 (p z)) := by
    funext z
    ext s
    exact (real z s).2
  rw [←hread]
  exact ManuscriptQLocalShiftIntegral.charge (cloud Q) (allocation D) X point hgood

section Charge
variable {D : ℕ} {X : ℂ→Grade Γ r} (hX : Ledger (allocation D) X)
include hX

theorem quiet (q : Index r) (z y : ℂ) :
    (X z).part (Join.pair Γ.quiet q)=(X y).part (Join.pair Γ.quiet q) := by
  obtain ⟨p,hp,he⟩ := hX (Join.pair Γ.quiet q)
  rw [pair_weight] at hp
  have h0 : p.natDegree≤0 := by
    change p.natDegree≤(∅:Finset V).card*D at hp
    simpa only [card_empty,zero_mul] using hp
  rw [←he z,←he y,Polynomial.eq_C_of_natDegree_le_zero h0]
  simp

theorem denominator (z y : ℂ) : Order.denominator (X z)=Order.denominator (X y) := by
  apply Join.both_parts
  intro s q
  by_cases h : s=Γ.quiet
  · simpa only [Order.denominator,Order.bottom_value,if_pos h] using quiet hX q z y
  · simp only [Order.denominator,Order.bottom_value,if_neg h]

theorem vacuum (z y : ℂ) : Order.logVac (X z)=Order.logVac (X y) := by
  unfold Order.logVac
  rw [denominator hX z y]

theorem connected : Ledger (allocation D) (fun z=>Order.logMarked (X z)) := by
  have hratio (z : ℂ) : Order.ratio (X z)=(X z)*Primitives.GCC.Anchor.inverseMass (Order.denominator (X 0)) := by
    unfold Order.ratio
    rw [denominator hX z 0]
  simpa only [Order.logMarked,hratio] using
    (hX.mul (Ledger.constant (Primitives.GCC.Anchor.inverseMass (Order.denominator (X 0))))).connected

theorem observed (k : ℕ) : Ledger (fun _:V=>D) (fun z=>Order.observe Γ r (X z) k) := by
  by_cases h : k≤r
  · have base : Ledger (fun _:V=>D) (fun z=>Poly.inject (fun s : Γ.Mode=>
        (X z).part (Join.pair s (Order.pick r k)))) := by
      intro s
      obtain ⟨p,hp,he⟩ := hX (Join.pair s (Order.pick r k))
      have hp' := hp.trans_eq (pair_weight D s (Order.pick r k))
      exact ⟨p,by rw [constant_weight]; exact hp',he⟩
    simpa only [Order.observe,if_pos h] using
      Ledger.smul ((k.factorial:ℂ)⁻¹) base
  · simpa only [Order.observe,if_neg h] using
      (Ledger.constant (w:=fun _:V=>D) (0:Poly Γ))

theorem cumulants (k : ℕ) : Ledger (fun _:V=>D)
    (fun z=>Order.observe Γ r (Order.logMarked (X z)) k) :=
  observed (connected hX) k

end Charge
end YM.Integration.ManuscriptQLocalWickLedger
end

section
/-! Every original finite graded marked forest gives a displacement
polynomial before taking its finite perturbative coefficient. Its complete
quiet denominator retains all unmarked coupling corrections. -/
namespace YM.Integration.ManuscriptQLocalForestPhases

open Filter Function Finset Lattice Wilson RG Marker Multi Exterior
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open Assembly Cumulants Tree Order ManuscriptQLocalShiftLedger
open scoped BigOperators Classical Topology

def basis {D : ℕ} (j : ZMod (D+1)) : Polynomial ℂ :=
  ∑k : ZMod (D+1),Polynomial.monomial k.val (ManuscriptQLocalSourceFourier.weight j k)

theorem basis_degree {D : ℕ} (j : ZMod (D+1)) : (basis j).natDegree≤D := by
  apply degree_sum
  intro k _
  exact (Polynomial.natDegree_monomial_le ..).trans (Nat.lt_succ_iff.mp (ZMod.val_lt k))

theorem basis_eval {D : ℕ} (j : ZMod (D+1)) (z : ℂ) :
    (basis j).eval z=ManuscriptQLocalPhaseJets.interpolation z j := by
  simp [basis,eval_sum,ManuscriptQLocalPhaseJets.interpolation,Polynomial.eval_monomial,mul_comm]

theorem interpolation {D : ℕ} (u : ZMod (D+1)→ℂ) :
    ∃p : Polynomial ℂ,p.natDegree≤D ∧
    ∀z,p.eval z=∑j,ManuscriptQLocalPhaseJets.interpolation z j*u j := by
  refine ⟨∑j,Polynomial.C (u j)*basis j,?_,?_⟩
  · apply degree_sum
    intro j _
    exact (Polynomial.natDegree_mul_le ..).trans (by simpa using basis_degree j)
  · intro z
    rw [eval_sum]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,basis_eval,mul_comm]

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {G : Gauge}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d) (Y : Bulk.Chain C.path)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
local notation "W" => ManuscriptQLocalEffectiveInput.colors F
local notation "K" => d.kernel Y
local notation "ph" => ManuscriptQLocalSourceFourier.phase
local notation "𝔽" => ZMod (F.packets.powerCap+1)

def array (Λ : Forest (S).ratio) (τ : (S).Choices) (B : fieldDir G (C.side d.level d.period) 1)
    (x : TestSpace J.tests) (r : ℕ) (z : ℂ) (e : Hot (Board Γ r)) :=
  Assembly.generator (Bulk.stage K Λ B) (Bulk.hinge Λ) (W z x).power
    (Bulk.markFn S Λ (W z x)) (Bulk.geometric K Λ τ (W z x)) r e

theorem vertex (hg : g₀≠0) (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (x : TestSpace J.tests) (r : ℕ)
    (v : Precision.Key Λ G→ℝ) (e : Hot (Board Γ r)) :
    ∃p : Polynomial ℂ,p.natDegree≤(Join.left e.val).val.card*F.packets.powerCap ∧
      ∀z,p.eval z=Cloud.paint v (array F Y Λ τ B x r z e) := by
  let n := (Join.right e.val).val.card
  let s := Join.left e.val
  by_cases hs : s.val.Nonempty
  · let a : Hot Γ := ⟨s,hs⟩
    let k := F.packets.powerCap+1+n
    let u := Assembly.translate (Bulk.stage K Λ B) (Bulk.hinge Λ) v
    obtain ⟨p,hp,hpval⟩ := interpolation (fun j : 𝔽=>
      (n.factorial:ℂ)*Assembly.jet (ManuscriptQLocalPhaseJets.field F Λ x a (ph j)) k u)
    have hc : F.packets.powerCap≤ s.val.card*F.packets.powerCap := by
      simpa only [one_mul] using Nat.mul_le_mul_right F.packets.powerCap (one_le_card.mpr hs)
    refine ⟨p,hp.trans hc,?_⟩
    intro z
    have hread : Cloud.paint v (array F Y Λ τ B x r z e)=
        (n.factorial:ℂ)*Assembly.jet (ManuscriptQLocalPhaseJets.field F Λ x a z) k u := by
      simp only [array,Assembly.generator,show (Join.left e.val).val.Nonempty from hs,
        dite_true,map_smul,Assembly.reading]
      rfl
    rw [hread,ManuscriptQLocalPhaseJets.radial F hg Λ x a z k u,hpval,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [smul_eq_mul]
    ring
  · refine ⟨Polynomial.C (Cloud.paint v (array F Y Λ τ B x r 0 e)),by simp,?_⟩
    intro z
    rw [Polynomial.eval_C]
    unfold array Assembly.generator
    simp only [show ¬(Join.left e.val).val.Nonempty from hs,dite_false]
    rfl

theorem raw (hg : g₀≠0) (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (x : TestSpace J.tests) (r : ℕ) :
    Ledger (ManuscriptQLocalWickLedger.allocation F.packets.powerCap)
      (fun z=>Bulk.Fk K Λ τ (W z x) B r) :=
  ManuscriptQLocalWickLedger.gaussian F.packets.powerCap ((K).covariance Λ τ)
    ((K).symm Λ τ) ((K).positive Λ τ).posSemidef (array F Y Λ τ B x r)
    (vertex F Y hg Λ τ B x r)

theorem denominator (hg : g₀≠0) (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (x : TestSpace J.tests)
    (r : ℕ) (z y : ℂ) :
    Order.denominator (Bulk.Fk K Λ τ (W z x) B r)=
      Order.denominator (Bulk.Fk K Λ τ (W y x) B r) :=
  ManuscriptQLocalWickLedger.denominator (raw F Y hg Λ τ B x r) z y

/-- Every mixed coefficient of the complete native marked normalized log
has a degree bound per occupied physical mode. -/
theorem original (hg : g₀≠0) (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (x : TestSpace J.tests) (r k : ℕ) :
    Ledger (fun _:V=>F.packets.powerCap) (fun z=>Order.observe Γ r
      (({d with forest:=Λ,tag:=τ,field:=B,colors:=W z x}).markedLog Y r) k) :=
  ManuscriptQLocalWickLedger.cumulants (raw F Y hg Λ τ B x r) k

end YM.Integration.ManuscriptQLocalForestPhases
end

section
/-! Restore source powers inside independently computed positive-coupling
finite trials. All sums are taken before the unique finite coefficients. -/
namespace YM.Integration.ManuscriptQLocalDiagonalTrial

open Filter Finset Comparison.RG02.Laplace PertExtension.Series
open PertExtension.Series.Tested
open scoped BigOperators Classical Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rise (a : ℕ→E) : ℕ→E
  | 0 => 0
  | k+1 => a k

def delay (s : ℕ) (a : ℕ→E) : ℕ→E :=
  Nat.rec a (fun _ b=>rise b) s

omit [NormedSpace ℝ E] in
theorem shifted (s k : ℕ) (a : ℕ→E) :
    delay s a k=if s≤k then a (k-s) else 0 := by
  induction s generalizing k with
  | zero => simp [delay]
  | succ s ih =>
    cases k with
    | zero => simp [delay,rise]
    | succ k =>
      change delay s a k=_
      simpa only [Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub] using ih k

theorem evaluate (a : ℕ→E) (n : ℕ) (t : ℝ) :
    peval (rise a) (n+1) t=t • peval a n t := by
  change (∑i∈range (n+1+1),t^i • rise a i)=t • ∑i∈range (n+1),t^i • a i
  rw [sum_range_succ',Finset.smul_sum]
  simp only [rise,pow_zero,one_smul,add_zero]
  apply sum_congr rfl
  intro i _
  rw [pow_succ,smul_smul,mul_comm]

theorem promoted {n : ℕ} {f : ℝ→E} (h : Bill n f) :
    Bill (n+1) (fun t=>t • f t) := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_pos] with t ht hpos
  rw [norm_smul,Real.norm_of_nonneg hpos.le,pow_succ]
  calc
    _ ≤ t*(C*t^n) := mul_le_mul_of_nonneg_left ht hpos.le
    _ = _ := by ring

theorem first {a : ℕ→E} {f : ℝ→E} (n : ℕ) (h : Trial a f n) :
    Trial (rise a) (fun t=>t • f t) n := by
  cases n with
  | zero =>
    have pe0 : peval a 0=(fun _:ℝ=>a 0) := by
      funext t
      change (∑i∈range 1,t^i • a i)=a 0
      simp
    have hb : Bill 1 (fun t=>f t-a 0) := by
      change Bill 1 (f-peval a 0) at h
      rw [pe0] at h
      exact h
    have hc : Bill 0 (fun _:ℝ=>a 0) := by
      simpa using (bill_mon (k:=0) (a 0) 0 (le_refl 0))
    have hd := bill_add (bill_ge hb (Nat.zero_le 1)) hc
    have hf : Bill 0 f := by
      simpa only [Pi.add_def,sub_add_cancel] using hd
    have eq : peval (rise a) 0=(0:ℝ→E) := by
      funext t
      change (∑i∈range 1,t^i • rise a i)=0
      simp [rise]
    change Bill 1 ((fun t:ℝ=>t • f t)-peval (rise a) 0)
    rw [eq,sub_zero]
    exact promoted hf
  | succ n =>
    have h' := trial_earlier (Nat.le_succ n) h
    unfold Trial at h' ⊢
    have raised := promoted h'
    convert raised using 1
    funext t
    simp only [Pi.sub_apply,evaluate,smul_sub]

theorem power {a : ℕ→E} {f : ℝ→E} {n : ℕ} (s : ℕ) (h : Trial a f n) :
    Trial (delay s a) (fun t=>t^s • f t) n := by
  induction s with
  | zero => simpa [delay] using h
  | succ s ih =>
    change Trial (rise (delay s a)) (fun t=>t^(s+1) • f t) n
    convert first n ih using 1
    funext t
    rw [pow_succ,smul_smul,mul_comm]

theorem sum {I : Type*} (S : Finset I) (a : I→ℕ→ℂ) (f : I→ℝ→ℂ) (n : ℕ)
    (h : ∀i∈S,Trial (a i) (f i) n) :
    Trial (∑i∈S,a i) (∑i∈S,f i) n := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have hz : (0:ℝ→ℂ)-peval (0:ℕ→ℂ) n=0 := by
      funext t
      simp [peval,Zone.eval]
    simpa only [Trial,hz] using (bill_zero (E:=ℂ) (n:=n+1))
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact trial_add (h i (mem_insert_self ..)) (ih (fun j hj=>h j (mem_insert_of_mem hj)))

/-- A growing original coupling and finitely many independently chosen
unit phases. Pure vacuum corrections in those trials remain untouched. -/
theorem assembled {D n : ℕ} (g : ℝ)
    (a : ZMod (D+1)→ℕ→ℂ) (f : ZMod (D+1)→ℝ→ℂ) {y : ℝ→ℂ}
    (h : ∀j,Trial (a j) (f j) n)
    (hy : ∀ᶠ t in along,y t=∑s : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j s*((t:ℂ)/(g:ℂ))^s.val*f j t) :
    Trial (fun k=>∑s : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j s/((g:ℂ)^s.val)*
        (if s.val≤k then a j (k-s.val) else 0)) y n := by
  let c := fun (j s : ZMod (D+1))=>ManuscriptQLocalSourceFourier.weight j s/((g:ℂ)^s.val)
  have paid (j s : ZMod (D+1)) := trial_scale (c j s) (power s.val (h j))
  have bought := sum univ (fun s=>∑j,c j s • delay s.val (a j))
    (fun s=>∑j,c j s • (fun t:ℝ=>t^s.val • f j t)) n
    (fun s _=>sum univ _ _ n (fun j _=>paid j s))
  have moved : (∑s : ZMod (D+1),∑j : ZMod (D+1),
      c j s • (fun t:ℝ=>t^s.val • f j t))=ᶠ[along] y := by
    filter_upwards [hy] with t ht
    rw [ht]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul,
      Complex.ofReal_pow,c,div_pow]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro j _
    ring
  have h' := trial_congr moved bought
  apply trial_flow h'
  intro k _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,shifted,c]

theorem original {D n : ℕ} (g : ℝ)
    (a : ZMod (D+1)→ℕ→ℂ) (f : ZMod (D+1)→ℝ→ℂ) {b : ℕ→ℂ} {y : ℝ→ℂ}
    (h : ∀j,Trial (a j) (f j) n) (hb : Trial b y n)
    (hy : ∀ᶠ t in along,y t=∑s : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j s*((t:ℂ)/(g:ℂ))^s.val*f j t) :
    ∀k≤n,b k=∑s : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j s/((g:ℂ)^s.val)*
        (if s.val≤k then a j (k-s.val) else 0) := by
  exact trial_gap hb (assembled g a f h hy)

end YM.Integration.ManuscriptQLocalDiagonalTrial
end

section
/-! Restore original source powers at the finite physical incoming field.
The fixed-correlated-direction rotation below uses the genuine original
radial W measure and the same fine point on every branch. -/
namespace YM.Integration.ManuscriptQLocalRadialDisplacement

open Filter Function MeasureTheory Finset Lattice Wilson RG Marker Multi Exterior
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open Assembly Cumulants Tree Order ManuscriptQLocalShiftLedger
open PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Classical Topology

/-- Extract the true one-sided finite trial from the native radial chart
on each original joint Gaussian direction. Its finite constants may depend
on the held direction. -/
theorem atPoint {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Zone T} {b : T→ℝ} {f : ℝ→T→E} {a : ℕ→T→E}
    (h : Z.Built b f a) (v : T) (r : ℕ) :
    Laplace.Trial (fun k=>a k v) (fun t=>f t v) r := by
  obtain ⟨δ,C,e,hδ,hC,hi⟩ := (h.fits r).cost
  have hw : 0<Z.w v := zero_lt_one.trans_le (Z.high v)
  have hb : 0≤b v := zero_le_one.trans ((h.fits r).envelope v)
  refine ⟨C*(Z.w v)^e*b v,mul_nonneg (mul_nonneg hC (pow_nonneg hw.le _)) hb,?_⟩
  filter_upwards [eventually_small (div_pos hδ hw)] with t ht
  exact hi v t ht.1 ((lt_div_iff₀ hw).mp ht.2).le

theorem expansion {V : Type} [DecidableEq V] [Fintype V] {S : Census V}
    {w : V→ℕ} (f : ℂ→Poly S) (hf : Ledger w f) (s : S.Mode)
    (D : ℕ) (hD : weight w s≤D) (z : ℂ) :
    (f z).part s=∑k : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j k*z^k.val*
        (f (ManuscriptQLocalSourceFourier.phase j)).part s := by
  obtain ⟨p,hp,he⟩ := hf s
  rw [←he,ManuscriptQLocalPhaseJets.evaluate p (hp.trans hD)]
  simp only [ManuscriptQLocalPhaseJets.interpolation,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro j _
  rw [he]
  ring

section fixed
variable {V : Type} [DecidableEq V] [Fintype V] {Γ:Census V} {G:Gauge}
  {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {J₀:Precision.ChartRatio G}
  (K:Bulk.Kernel S p P J₀) (Λ:Forest S.ratio) (τ:S.Choices) (B:fieldDir G c 1)
  (v:Precision.Key Λ G→ℝ)

def measured (W₀ : Bulk.Colors Γ G f) (t : ℝ) : Poly Γ :=
  Assembly.numeric W₀.power (Bulk.markFn S Λ W₀) (Bulk.geometric K Λ τ W₀) t
    (Bulk.translated K Λ B v)

def price (W₀ : Bulk.Colors Γ G f) (t : ℝ) : ℂ :=
  Real.exp (Radial.higher (Bulk.geometric K Λ τ W₀) t (Bulk.translated K Λ B v))

def row (W₀ : Bulk.Colors Γ G f) (s : Γ.Mode) (k : ℕ) : ℂ :=
  Assembly.rows (Assembly.expansions W₀.power (Bulk.markFn S Λ W₀)
    (Bulk.geometric K Λ τ W₀)) s k (Bulk.translated K Λ B v)

theorem material (W₀ : Bulk.Colors Γ G f) (t : ℝ) :
    measured K Λ τ B v W₀ t=price K Λ τ B v W₀ t •
      Poly.pass (Integral.markedLog t (Λ.drape (Integral.walk K Λ t B v)) W₀) := by
  rw [measured,Assembly.numeric,Poly.product_bead,Integral.numerator_mark]
  rfl

theorem trial (W₀ : Bulk.Colors Γ G f)
    (hw : Bulk.Well W₀) (s : Γ.Mode) (r : ℕ) :
    Laplace.Trial (row K Λ τ B v W₀ s) (fun t=>(measured K Λ τ B v W₀ t).part s) r :=
  atPoint (Assembly.radial_comparison _ _ _ (Bulk.geometric_ready K Λ τ W₀ hw)
    (show 0<(1:ℝ) by norm_num) s) (Bulk.translated K Λ B v) r

end fixed

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {G : Gauge}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d) (Y : Bulk.Chain C.path)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
local notation "W" => ManuscriptQLocalEffectiveInput.colors F
local notation "K" => d.kernel Y
local notation "ph" => ManuscriptQLocalSourceFourier.phase


/-- Actual fine field, common vacuum factor, all original independent
marked partners, at every nonzero coupling. The finite Fourier bank is
chosen before the fine configuration and signed polarization. -/
theorem physical (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (v : Precision.Key Λ G→ℝ)
    (hg : g₀≠0) (x : TestSpace J.tests) (s : Γ.Mode)
    (D : ℕ) (hD : weight (fun _:V=>F.packets.powerCap) s≤D) (t : ℝ) (ht : t≠0) :
    (measured (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (F.colors x) t).part s=
      ∑q : ZMod (D+1),∑j : ZMod (D+1),
        ManuscriptQLocalSourceFourier.weight j q*((t:ℂ)/(g₀:ℂ))^q.val*
          (measured (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (W (ph j) x) t).part s := by
  let U := Λ.drape (Integral.walk K Λ t B v)
  let w := price (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (F.colors x) t
  have old : (measured (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (F.colors x) t).part s=
      w*(Poly.pass (F.packets.read x t U)).part s := by
    rw [material,Poly.part_smul,F.convention.marks x t ht]
  have unit (j : ZMod (D+1)) : (measured (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (W (ph j) x) t).part s=
      w*(Poly.pass ((ManuscriptQLocalPacketGrades.phaseSource F.packets g₀ (ph j)).read x t U)).part s := by
    rw [material,Poly.part_smul,
      (ManuscriptQLocalEffectiveInput.convention F hg (ph j)
        (ManuscriptQLocalSourceFourier.unit j)).marks x t ht]
    rfl
  rw [old,←ManuscriptQLocalPacketGrades.phase_recovery F.packets ht hg]
  rw [expansion _ (ManuscriptQLocalPhaseMark.ordinary F.input_paid hg x t U) s D hD,
    Finset.mul_sum]
  apply sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  rw [unit]
  ring

/-- Shifted original finite before-integration coefficients. No physical
step approximation and no cut/winding replacement enters this identity. -/
theorem finite (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (v : Precision.Key Λ G→ℝ)
    (hg : g₀≠0) (x : TestSpace J.tests) (s : Γ.Mode)
    (D : ℕ) (hD : weight (fun _:V=>F.packets.powerCap) s≤D) (r k : ℕ) (hk : k≤r) :
    row (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (F.colors x) s k =
      ∑q : ZMod (D+1),∑j : ZMod (D+1),
        ManuscriptQLocalSourceFourier.weight j q/((g₀:ℂ)^q.val)*
          (if q.val≤k then row (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (W (ph j) x) s (k-q.val) else 0) := by
  apply ManuscriptQLocalDiagonalTrial.original g₀
    (fun j : ZMod (D+1)=>row (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (W (ph j) x) s)
    (fun j t=>(measured (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v (W (ph j) x) t).part s)
    (fun j=>trial (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v _ ((ManuscriptQLocalEffectiveInput.convention F hg (ph j)
      (ManuscriptQLocalSourceFourier.unit j)).well x) s r)
    (trial (Γ:=Γ) (G:=G) («S»:=S) K Λ τ B v _ (F.convention.well x) s r) ?_ k hk
  filter_upwards [eventually_pos] with t ht
  exact physical F Y Λ τ B v hg x s D hD t ht.ne'

end YM.Integration.ManuscriptQLocalRadialDisplacement
end

section
/-! The genuine finite normalized-grade input numerator commutes with
restoration of the original coupling powers at every forest and pin.
Gaussian integrals are taken only after the pointwise local coefficients
are identified. -/
namespace YM.Integration.ManuscriptQLocalMeasuredDisplacement
open Filter Function MeasureTheory Finset Lattice Wilson RG Marker Multi Exterior
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open Assembly Cumulants Tree Order ManuscriptQLocalShiftLedger Next.SectorChange
open ManuscriptQLocalRadialDisplacement
open scoped BigOperators Classical Topology

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {G : Gauge}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d) (Y : Bulk.Chain C.path)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
local notation "W" => ManuscriptQLocalEffectiveInput.colors F
local notation "K" => d.kernel Y
local notation "ph" => ManuscriptQLocalSourceFourier.phase

abbrev cloudCov (d₀:LocalFormal.Datum C Γ) (Y₀:Bulk.Chain C.path)
    (F₀:Forest (C.path.levels.clock.op d₀.level d₀.period).ratio)
    (t₀:(C.path.levels.clock.op d₀.level d₀.period).Choices) :=
  Gaussian.cloud ((d₀.kernel Y₀).covariance F₀ t₀)

theorem moment (Λ : Forest (S).ratio) (τ : (S).Choices) (B : fieldDir G (C.side d.level d.period) 1)
    (W₀ : Bulk.Colors Γ G (C.side (d.level+1) d.period)) (s : Γ.Mode)
    (r k : ℕ) (_hk : k≤r) :
    Integrable (fun v=>row K Λ τ B v W₀ s k) (cloudCov d Y Λ τ) ∧
    (Order.observe Γ r (Bulk.Fk K Λ τ W₀ B r) k).part s=∫v,row K Λ τ B v W₀ s k ∂(cloudCov d Y Λ τ) := by
  have h := Assembly.gather (Bulk.stage K Λ B) (Bulk.hinge Λ) W₀.power
    (Bulk.markFn S Λ W₀) (Bulk.geometric K Λ τ W₀) ((K).covariance Λ τ) ((K).symm Λ τ)
    ((K).positive Λ τ) s (Order.pick r k)
  simp only [Order.picked r _hk] at h
  refine ⟨h.1,?_⟩
  have fac : (k.factorial:ℂ)≠0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  apply mul_left_cancel₀ fac
  exact (Order.observed (x:=Bulk.Fk K Λ τ W₀ B r) s _hk).trans h.2

theorem raw (Λ : Forest (S).ratio) (τ : (S).Choices) (B : fieldDir G (C.side d.level d.period) 1)
    (hg : g₀≠0) (x : TestSpace J.tests) (s : Γ.Mode)
    (D : ℕ) (hD : weight (fun _:V=>F.packets.powerCap) s≤D)
    (r k : ℕ) (hk : k≤r) :
    (Order.observe Γ r (Bulk.Fk K Λ τ (F.colors x) B r) k).part s =
    ∑q : ZMod (D+1),∑j : ZMod (D+1),
      ManuscriptQLocalSourceFourier.weight j q/((g₀:ℂ)^q.val)*
        (if q.val≤k then (Order.observe Γ r (Bulk.Fk K Λ τ (W (ph j) x) B r)
          (k-q.val)).part s else 0) := by
  let c := fun (j q : ZMod (D+1))=>ManuscriptQLocalSourceFourier.weight j q/((g₀:ℂ)^q.val)
  let branch := fun (j q : ZMod (D+1)) v=>c j q*
    (if q.val≤k then row K Λ τ B v (W (ph j) x) s (k-q.val) else 0)
  have hi (j q : ZMod (D+1)) : Integrable (branch j q) (cloudCov d Y Λ τ) := by
    by_cases hq : q.val≤k
    · simpa [branch,hq] using (moment Y Λ τ B (W (ph j) x) s r (k-q.val)
        ((Nat.sub_le ..).trans hk)).1.const_mul (c j q)
    · simp [branch,hq]
  rw [(moment Y Λ τ B (F.colors x) s r k hk).2]
  calc
    _ = ∫v,∑q : ZMod (D+1),∑j : ZMod (D+1),branch j q v ∂(cloudCov d Y Λ τ) :=
      integral_congr_ae (ae_of_all _ (fun v=>
        ManuscriptQLocalRadialDisplacement.finite F Y Λ τ B v hg x s D hD r k hk))
    _ = _ := by
      rw [integral_finsetSum _ (fun q _=>integrable_finsetSum _ (fun j _=>hi j q))]
      apply sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun j _=>hi j q)]
      apply sum_congr rfl
      intro j _
      by_cases hq : q.val≤k
      · simp only [branch,if_pos hq,integral_const_mul,c]
        rw [(moment Y Λ τ B (W (ph j) x) s r (k-q.val) ((Nat.sub_le ..).trans hk)).2]
      · simp [branch,hq]

theorem enough (s : Γ.Mode) :
    weight (fun _:V=>F.packets.powerCap) s≤Fintype.card V*F.packets.powerCap := by
  rw [ManuscriptQLocalWickLedger.constant_weight]
  exact Nat.mul_le_mul_right F.packets.powerCap (Finset.card_le_univ s.val)

end YM.Integration.ManuscriptQLocalMeasuredDisplacement
end

section
/-! Full finite marked logarithmic coefficient after restoring the
original coupling weights. Both the physical and algebraic log carry the
same complete vacuum denominator through the finite horizon. -/
namespace YM.Integration.ManuscriptQLocalFiniteDisplacement

open Filter Function Finset Lattice Wilson RG Marker Multi Exterior
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open Assembly Cumulants Tree Order Extra.Trajectories ManuscriptQLocalShiftLedger
open PertExtension.Series.Tested
open scoped BigOperators Classical Topology

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {r : ℕ}

theorem values {D : ℕ} {X : ℂ→Grade Γ r}
    (hX : Ledger (ManuscriptQLocalWickLedger.allocation D) X) (t : ℝ) :
    Ledger (fun _:V=>D) (fun z=>Order.value (t:ℂ) (X z)) :=
  Ledger.sum (range (r+1)) _ (fun k=>
    Ledger.smul ((t:ℂ)^k) (ManuscriptQLocalWickLedger.observed hX k))

omit [Fintype V] in
theorem mass {w : V→ℕ} {f : ℂ→Poly Γ} (hf : Ledger w f) (z y : ℂ) :
    (f z).part Γ.quiet=(f y).part Γ.quiet := by
  obtain ⟨p,hp,he⟩ := hf Γ.quiet
  have hd : p.natDegree≤0 := by
    change p.natDegree≤∑a∈(∅:Finset V),w a at hp
    simpa only [sum_empty] using hp
  rw [←he z,←he y,Polynomial.eq_C_of_natDegree_le_zero hd]
  simp

theorem tested (x : Grade Γ r) :
    Laplace.Fleet.Test x (fun t=>Order.value (t:ℂ) x) := by
  intro s
  have h : (fun t:ℝ=>(Order.value (t:ℂ) x).part s)-peval (Laplace.detail x s) r=0 := by
    funext t
    simp only [Pi.sub_apply,Laplace.tests,sub_self,Pi.zero_apply]
  simpa only [Laplace.Trial,h] using (Laplace.bill_zero (E:=ℂ) (n:=r+1))

section Clock
variable {D N : ℕ} {x : Grade Γ r} {X : ℂ→Grade Γ r} (g : ℝ)
    (hx : Ledger (ManuscriptQLocalWickLedger.allocation D) X)
    (hN : ∀s : Γ.Mode,weight (fun _:V=>D) s≤N)
local notation "I" => ZMod (N+1)
local notation "φ" => ManuscriptQLocalSourceFourier.phase
local notation "c" => ManuscriptQLocalSourceFourier.weight

/-- Proper lower-perturbative displacement of the finite numerator at the
sampled coupling, on a bank fixed before any nonvacuum pin. -/
def Raw (x : Grade Γ r) (X : ℂ→Grade Γ r) (N : ℕ) (g : ℝ) :=
  ∀s : Γ.Mode,∀k≤r,Laplace.detail x s k=
    ∑q : ZMod (N+1),∑j : ZMod (N+1),
      ManuscriptQLocalSourceFourier.weight j q/((g:ℂ)^q.val)*
        (if q.val≤k then Laplace.detail (X (φ j)) s (k-q.val) else 0)

include hx hN in
theorem diagonal (hb : Raw x X N g) :
    Laplace.Fleet.Test x (fun t=>Order.value (t:ℂ) (X ((t:ℂ)/(g:ℂ)))) := by
  intro s
  have source (t : ℝ) := ManuscriptQLocalRadialDisplacement.expansion _
    (values hx t) s N (hN s) ((t:ℂ)/(g:ℂ))
  have hy := ManuscriptQLocalDiagonalTrial.assembled g (fun j : I=>Laplace.detail (X (φ j)) s)
      (fun j t=>(Order.value (t:ℂ) (X (φ j))).part s) (fun j=>tested (X (φ j)) s)
      (Eventually.of_forall source)
  exact Laplace.trial_flow hy (fun k hk=>(hb s k hk).symm)

include hx hN in
theorem logs (hb : Raw x X N g) (h₀ : UnitLeading x) (hs₀ : Symmetric x)
    (hp : ∀j : I,UnitLeading (X (φ j))) (hsp : ∀j : I,Symmetric (X (φ j))) :
    Raw (Order.logMarked x) (fun z=>Order.logMarked (X z)) N g := by
  intro s
  have old := Laplace.Fleet.connected_series h₀ (diagonal g hx hN hb) hs₀ s
  have point (t : ℝ) := ((values hx t).normalized (fun z=>mass (values hx t) z 0)).connected
  have source (t : ℝ) := ManuscriptQLocalRadialDisplacement.expansion _
    (point t) s N (hN s) ((t:ℂ)/(g:ℂ))
  have one (j : I) := Laplace.Fleet.connected_series (hp j) (tested (X (φ j))) (hsp j) s
  exact ManuscriptQLocalDiagonalTrial.original g
    (fun j : I=>Laplace.detail (Order.logMarked (X (φ j))) s)
    (fun j t=>(connected (Order.unitScale (Order.value (t:ℂ) (X (φ j))))).part s)
    one old (Eventually.of_forall source)

end Clock

variable {G : Gauge} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {d : LocalFormal.Datum C Γ} (F : AnalyticInput J A d) (Y : Bulk.Chain C.path)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
local notation "W" => ManuscriptQLocalEffectiveInput.colors F
local notation "K" => d.kernel Y
local notation "φ" => ManuscriptQLocalSourceFourier.phase

/-- True original finite signed coefficient at every physical marking,
with independent geometry, placements, correlated free coordinates and
the whole source normalization. The separate infinite presentation may
then spend its own two rooted comparison prices. -/
theorem original (hg : g₀≠0) (Λ : Forest (S).ratio) (τ : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (z : TestSpace J.tests) (r : ℕ) :
    Raw (({d with forest:=Λ,tag:=τ,field:=B,colors:=F.colors z}).markedLog Y r)
      (fun y=>({d with forest:=Λ,tag:=τ,field:=B,colors:=W y z}).markedLog Y r)
      (Fintype.card V*F.packets.powerCap) g₀ := by
  apply logs g₀ (ManuscriptQLocalForestPhases.raw F Y hg Λ τ B z r)
    (ManuscriptQLocalMeasuredDisplacement.enough F)
  · intro s k hk
    exact ManuscriptQLocalMeasuredDisplacement.raw F Y Λ τ B hg z s _
      (ManuscriptQLocalMeasuredDisplacement.enough F s) r k hk
  · exact Bulk.fk_unit ..
  · exact Bulk.fk_sym ..
  · intro j
    exact Bulk.fk_unit ..
  · intro j
    exact Bulk.fk_sym ..

end YM.Integration.ManuscriptQLocalFiniteDisplacement
end
