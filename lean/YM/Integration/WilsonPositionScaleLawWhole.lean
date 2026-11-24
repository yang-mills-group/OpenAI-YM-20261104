import YM.Integration.WilsonPositionScaleLawSingleGrade

/-! The exact original fixed-field equation in every grade of the same positioned
tower. The lower block is strictly contracting at the physical half-scale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawWhole
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (positioned Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawGrade (grade lift reads half)
open WilsonPositionScaleLawFixed (top)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{d:ℕ}

def low (C:Family G)(v:(Bel C.book).Field d):ℝ:=∑i∈Finset.univ.erase (top d),‖grade C i v‖
def fee (C:Family G)(d:ℕ):ℝ:=∑i∈Finset.univ.erase (top d),‖grade C i‖

theorem sumAll (C:Family G)(v:(Bel C.book).Field d):∑i:Fin (d+1),grade C i v=v:=by
  apply (fields C.labels d).injective
  simp only [map_sum,WilsonPositionScaleLawGrade.grade,reads]
  exact Level.all _

theorem split (C:Family G)(v:(Bel C.book).Field d):‖v‖≤low C v+‖grade C (top d) v‖:=by
  calc
    _=‖∑i:Fin (d+1),grade C i v‖:=by rw [sumAll]
    _≤∑i:Fin (d+1),‖grade C i v‖:=norm_sum_le ..
    _=_:=(Finset.sum_erase_add _ _ (Finset.mem_univ (top d))).symm

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def full (d:ℕ)(r:ℝ)(O:S.Field d):E d:=(r:ℂ)^d • (positioned F J Z.store r d).symm O

theorem step (r:ℝ)(t:Ratio)(i:Fin (d+1))(O:S.Field d):
    grade R.family i (exactOp F J Z.store d (r,t) (full F J Z d (t.val*r) O))=
      (t.val:ℂ)^(d-i.val) • grade R.family i (full F J Z d r O):=by
  let T:=positioned F J Z.store
  let U:=exactOp F J Z.store d (r,t)
  let P:=grade R.family i
  let v:=(T (t.val*r) d).symm O
  have home:(T r d).symm O=Pert.Scale.gear R.family.labels d t.val (U v):=by
    apply (T r d).injective
    change T r d ((T r d).symm O)=T r d (Pert.Scale.gear R.family.labels d t.val (Frame.cocycle d T r t.val (WilsonPositionScaleLawNative.positive t) v))
    rw [Frame.cocycle_value,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change P (U (((↑(t.val*r):ℂ)^d) • v))=(t.val:ℂ)^(d-i.val) • P (((r:ℂ)^d) • (T r d).symm O)
  rw [U.map_smul,P.map_smul,P.map_smul,home,WilsonPositionScaleLawFixed.engineering,smul_smul,smul_smul]
  congr 1
  have power:(t.val:ℂ)^(d-i.val)*(t.val:ℂ)^i.val=(t.val:ℂ)^d:=by
    rw [←pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
  rw [Complex.ofReal_mul,mul_pow,←power]
  ring

end YM.Integration.WilsonPositionScaleLawWhole
end
