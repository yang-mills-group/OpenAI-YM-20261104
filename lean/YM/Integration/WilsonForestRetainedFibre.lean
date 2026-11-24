import YM.Integration.WilsonPhysicalRegisteredForestConditional
import YM.Integration.WilsonHeldRetainedWindows

/-! The retained original action on the actual free-link integration fibre.
The exterior remains distributed by its full, interacting Wilson marginal. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonForestRetainedFibre
open Function Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open WilsonPhysicalRegisteredForestAction OriginalMarkedRunAction
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "k" => (j+1)
local notation "op" => R.family.path.levels.clock.op j per
local notation "fine" => Config G (R.family.side k per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per k
local notation "held" => WilsonHeldExteriorLaw.weight R N per j

theorem fixed (T : Forest (op).ratio) (E : Finset T.Free) (S : Support (R.family.side k per)) (tails : ∀ e∈E, e.val.1∈S)
    (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) (x y : (↥E → G.El)) : OriginalMarkedLocalDifference.Outside S (filled (S:=op) (G:=G) T E v x) (filled (S:=op) (G:=G) T E v y) := by
  intro e he
  by_cases tree : e∈T.trunks
  · exact (T.on_tree _ ⟨e,tree⟩).trans (T.on_tree _ ⟨e,tree⟩).symm
  · let i : T.Free := ⟨e,tree⟩
    have rem : i ∉ E := fun mem => he (tails i mem)
    have keep (z : (↥E → G.El)) : filled (S:=op) (G:=G) T E v z e = v ⟨i,rem⟩ := by
      change T.drape ((cut (S:=op) (G:=G) T E).symm (z,v)) i = _
      rw [T.off_tree]
      exact congrFun (congrArg Prod.snd ((cut (S:=op) (G:=G) T E).apply_symm_apply (z,v))) ⟨i,rem⟩
    exact (keep x).trans (keep y).symm

def mass (T : Forest (op).ratio) (E : Finset T.Free) (V : coarse) (P : Rep G (R.family.side k per)) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) : ℝ :=
  ∫ x, held V P (filled (S:=op) (G:=G) T E v x) ∂Chart.physical G (↥E)

def corrected (T : Forest (op).ratio) (E : Finset T.Free) (V : coarse) (P : Rep G (R.family.side k per)) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) (U : fine) : ℝ :=
  held V P U * mass R (N:=N) T E V (up) v / mass R (N:=N) T E V P v

theorem envelope (T : Forest (op).ratio) (E : Finset T.Free) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) {h : fine→ℝ} (env : Envelope h) :
    Envelope (fun x : (↥E → G.El) => h (filled (S:=op) (G:=G) T E v x)) :=
  ⟨env.meas.comp (T.continuous_drape.measurable.comp ((cut (S:=op) (G:=G) T E).symm.measurable.comp
      (measurable_id.prodMk measurable_const))),env.cost.choose,fun x => env.cost.choose_spec (filled (S:=op) (G:=G) T E v x)⟩

/-- On one fixed physical forest exterior, including a possible empty set of
free links, the exact marginal correction pays a single action oscillation.
The pricing support counts actual changed link tails. -/
theorem original (T : Forest (op).ratio) (E : Finset T.Free) {d : ℕ} (interior : k<N) (A : Comparison R (p:=per) interior d)
    (S : Support (R.family.side k per)) (tails : ∀ e∈E,e.val.1∈S) (V : coarse) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) (x : (↥E → G.El)) :
    let P := approximation R (p:=per) interior d
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (k+1))^(d+1))
    let U := filled (S:=op) (G:=G) T E v x
    0 < mass R (N:=N) T E V P v ∧ Real.exp (-a)*held V (up) U ≤ corrected R (N:=N) T E V P v U ∧
      corrected R (N:=N) T E V P v U ≤ Real.exp a*held V (up) U := by
  intro P a U
  letI : IsProbabilityMeasure (Chart.physical G (↥E)) := by unfold Chart.physical;infer_instance
  let X := filled (S:=op) (G:=G) T E v
  let p (Y : fine) := held V P Y
  let q (Y : fine) := held V (up) Y
  let J (Y : fine) := (remainder R (p:=per) interior d).additive (R.alloy.B.a.budget k) Y
  obtain ⟨pc,hpc,pmin⟩ := OriginalMarkedGibbsAction.retained_floor R interior A
  obtain ⟨pe,gi,hg,lo⟩ := WilsonHeldExteriorLaw.regularity R N per j interior.le V P
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hpc pmin
  obtain ⟨qc,hqc,qmin⟩ := WilsonHeldExteriorLaw.upper_floor R N per j interior.le
  have qe := (WilsonHeldExteriorLaw.regularity R N per j interior.le V (up)
    ((up).envelope (R.makes.wilson.represents N per k interior.le).good) hqc qmin).1
  have pi : Integrable (fun y => p (X y)) (Chart.physical G (↥E)) := (envelope R T E v pe).integrable (Chart.physical G (↥E))
  have qi : Integrable (fun y => q (X y)) (Chart.physical G (↥E)) := (envelope R T E v qe).integrable (Chart.physical G (↥E))
  have floor : gi ≤ mass R (N:=N) T E V P v := by
    change gi ≤ ∫ y, p (X y) ∂Chart.physical G (↥E)
    have h := integral_mono (integrable_const (μ:=(Chart.physical G (↥E))) gi) pi (fun y => lo (X y))
    simpa only [integral_const,probReal_univ,one_smul] using h
  have zp : 0 < mass R (N:=N) T E V P v := hg.trans_le floor
  have law (Y : fine) : q Y = p Y * Real.exp (-J Y) := by
    have factor : (up).eval Y = P.eval Y * Real.exp (-J Y) := OriginalMarkedRunCovariance.factor R interior A Y
    change held V (up) Y = held V P Y * _
    unfold WilsonHeldExteriorLaw.weight
    rw [factor]
    simp only [div_eq_mul_inv]
    ac_rfl
  have pos (Y : fine) : 0 < q Y := (law Y).symm ▸ mul_pos (hg.trans_le (lo Y)) (Real.exp_pos _)
  have signed (Y : fine) : -Real.log ((up).eval Y) + Real.log (P.eval Y) = J Y := A.signed Y
  have pair (y : (↥E → G.El)) :
      (Real.exp (-a)*q U)*p (X y) ≤ p U*q (X y) ∧ p U*q (X y) ≤ (Real.exp a*q U)*p (X y) := by
    have bound := OriginalMarkedLocalPurchase.run R interior A S U (X y) (fixed R T E S tails v x y)
    change |(-Real.log ((up).eval U)+Real.log (P.eval U))-(-Real.log ((up).eval (X y))+Real.log (P.eval (X y)))| ≤ a at bound
    rw [signed U,signed (X y)] at bound
    have h := abs_le.mp bound
    have charge : Real.exp (-J U)*Real.exp (J U-J (X y)) = Real.exp (-J (X y)) := by
      rw [←Real.exp_add,show -J U+(J U-J (X y)) = -J (X y) by ring]
    have eq : p U*q (X y) = (q U*p (X y))*Real.exp (J U-J (X y)) := by
      rw [law (X y),law U,←charge];ring
    rw [eq]
    have positive := mul_nonneg (pos U).le ((hg.trans_le (lo (X y))).le)
    constructor
    · calc _ = (q U*p (X y))*Real.exp (-a) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h.1) positive
    · calc _ ≤ (q U*p (X y))*Real.exp a := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h.2) positive
           _ = _ := by ring
  have lower := integral_mono (pi.const_mul (Real.exp (-a)*q U)) (qi.const_mul (p U)) (fun y => (pair y).1)
  have upper := integral_mono (qi.const_mul (p U)) (pi.const_mul (Real.exp a*q U)) (fun y => (pair y).2)
  simp only [integral_const_mul] at lower upper
  exact ⟨zp,(le_div_iff₀ zp).mpr lower,(div_le_iff₀ zp).mpr upper⟩

end YM.Integration.WilsonForestRetainedFibre
