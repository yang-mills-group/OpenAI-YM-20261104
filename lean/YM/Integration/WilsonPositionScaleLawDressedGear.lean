import YM.Integration.WilsonPositionScaleLawWhole

/-! A uniform numerical price for undoing the original engineering dilation on
the retained Maxwell space, in its actual transported field norm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawDressedGear
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawNative (positive)
open WilsonPositionScaleLawGrade (grade)
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G){d:ℕ}

def engine (d:ℕ)(t:Ratio):(Bel C.book).Field d→L[ℂ](Bel C.book).Field d:=
  (Pert.Scale.gear C.labels d t.val).toContinuousLinearMap

def cap (d:ℕ):ℝ:=∑i:Fin (d+1),(2:ℝ)^i.val*‖grade C i‖
theorem capPositive:0≤cap C d:=by
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  exact Finset.sum_nonneg fun _ _=>mul_nonneg (by positivity) (norm_nonneg _)

theorem component (i:Fin (d+1))(t:Ratio)(v:(Bel C.book).Field d):
    ‖grade C i v‖≤(2:ℝ)^i.val*‖grade C i‖*‖engine C d t v‖:=by
  have e:‖grade C i (engine C d t v)‖=t.val^i.val*‖grade C i v‖:=by
    change ‖grade C i (Pert.Scale.gear C.labels d t.val v)‖=_
    rw [WilsonPositionScaleLawFixed.engineering,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive t)]
  have length:1≤(2:ℝ)*t.val:=by linarith [t.property.1]
  calc
    _≤(2*t.val)^i.val*‖grade C i v‖:=le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ length)
    _=(2:ℝ)^i.val*‖grade C i (engine C d t v)‖:=by rw [e,mul_pow];ring
    _≤(2:ℝ)^i.val*(‖grade C i‖*‖engine C d t v‖):=mul_le_mul_of_nonneg_left ((grade C i).le_opNorm _) (by positivity)
    _=_:=by ring

theorem inverse (t:Ratio)(v:(Bel C.book).Field d):‖v‖≤cap C d*‖engine C d t v‖:=by
  calc
    _=‖∑i:Fin (d+1),grade C i v‖:=by rw [WilsonPositionScaleLawWhole.sumAll]
    _≤∑i:Fin (d+1),‖grade C i v‖:=norm_sum_le ..
    _≤∑i:Fin (d+1),(2:ℝ)^i.val*‖grade C i‖*‖engine C d t v‖:=Finset.sum_le_sum fun i _=>component C i t v
    _=_:=by rw [cap,Finset.sum_mul]

end YM.Integration.WilsonPositionScaleLawDressedGear
