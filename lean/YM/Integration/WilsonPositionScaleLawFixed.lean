import YM.Integration.WilsonPositionScaleLawDyadic

/-! Exact recurrence of a fixed original physical field on its highest surviving
grade. The dyadic engineering factor is cancelled at each step in the same
Maxwell units. No fitted intermediate basis or unrelated infrared target enters. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawFixed
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (positioned Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawGrade (grade lift reads half)
open WilsonPositionScaleLawClock (radius)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{d:ℕ}

def top (d:ℕ):Fin (d+1):=⟨d,Nat.lt_succ_self _⟩

private theorem diagonalSector (i:Fin (d+1))(s:ℝ)(x:Sec G d):
    Level.proj i (Level.Dial d s x)=Extent.token s i.val • Level.proj i x:=by
  simp only [Level.Dial,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  rw [Finset.sum_eq_single i]
  · rw [Level.again]
  · intro j _ hj;rw [Level.distinct _ _ _ (Ne.symm hj),smul_zero]
  · simp

private theorem peak {A:FieldEnd G d}(h:Level.Band A)(x:Sec G d):
    Level.proj (top d) (A x)=Level.proj (top d) (A (Level.proj (top d) x)):=by
  calc
    _=Level.proj (top d) (A (∑i:Fin (d+1),Level.proj i x)):=by rw [Level.all]
    _=_:=by
      rw [map_sum,map_sum,Finset.sum_eq_single (top d)]
      · intro j _ hj
        have lt:j<top d:=lt_of_le_of_ne (show j≤top d from Level.within j) hj
        exact Level.stop x (top d) h j lt
      · simp

private theorem respects {d:ℕ}(a:MoveSpace G d):Level.Band (WilsonPhysicalPositionDiscreteBranches.field a):=by
  intro j hj p hp
  exact Submodule.add_mem _ hp (((guide G d).symm a).property.2.1 j hj p hp)

variable (C)

theorem idempotent (i:Fin (d+1))(v:(Bel C.book).Field d):grade C i (grade C i v)=grade C i v:=by
  apply (fields C.labels d).injective
  simp only [WilsonPositionScaleLawGrade.grade,reads,Level.again]

theorem engineering (i:Fin (d+1))(t:Ratio)(v:(Bel C.book).Field d):
    grade C i (Pert.Scale.gear C.labels d t.val v)=(t.val:ℂ)^i.val • grade C i v:=by
  apply (fields C.labels d).injective
  rw [reads,map_smul,reads,WilsonPositionScaleLawUnits.original,diagonalSector,Extent.token,WilsonPositionScaleLawIndependent.geometry]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

private theorem projected (lead:Leading F J)(d:ℕ):∀ᶠr in trail,∀v:E d,
    grade R.family (top d) (exactOp F J Z.store d (r,half) v)=
      grade R.family (top d) (exactOp F J Z.store d (r,half) (grade R.family (top d) v)):=by
  have pin:Tendsto (fun r:ℝ=>(r,half)) trail sweep:=tendsto_id.prodMk tendsto_top
  filter_upwards [pin.eventually (WilsonPositionScaleLawNative.realizes F J Z.store lead d)] with r hu v
  rw [←hu]
  apply (fields R.family.labels d).injective
  let a:=WilsonPositionScaleLawNative.coordinates F J Z.store d (r,half)
  let A:=WilsonPhysicalPositionDiscreteBranches.field a
  change fields R.family.labels d (grade R.family (top d) (lift R.family A v))=
    fields R.family.labels d (grade R.family (top d) (lift R.family A (grade R.family (top d) v)))
  rw [reads,reads,reads,reads,reads]
  exact peak (respects a) _

def normalized (d:ℕ)(r:ℝ)(n:ℕ)(O:S.Field d):E d:=
  (radius r n:ℂ)^d • grade R.family (top d) ((positioned F J Z.store (radius r n) d).symm O)

theorem balance (lead:Leading F J)(d:ℕ)(r:ℝ)(hr:0<r):∀ᶠn:ℕ in atTop,∀O:S.Field d,
    normalized F J Z d r n O=WilsonPositionScaleLawDyadic.step Z F J (top d) r n (normalized F J Z d r (n+1) O):=by
  let T:=positioned F J Z.store
  let P:=grade R.family (top d)
  filter_upwards [(WilsonPositionScaleLawClock.falls r hr).eventually (projected F J Z lead d)] with n equal O
  let h:=radius r n
  let t:=half.val
  let v:=(T (t*h) d).symm O
  let U:=exactOp F J Z.store d (h,half)
  let D:=WilsonPositionScaleLawDyadic.step Z F J (top d) r n
  have ns:radius r (n+1)=t*h:=by dsimp [t,h,radius,half];ring
  have old:(T h d).symm O=Pert.Scale.gear R.family.labels d t (U v):=by
    apply (T h d).injective
    change T h d ((T h d).symm O)=T h d (Pert.Scale.gear R.family.labels d t (Frame.cocycle d T h t (WilsonPositionScaleLawNative.positive half) v))
    rw [Frame.cocycle_value,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  have take:D (P v)=P (U v):=(WilsonPositionScaleLawDyadic.read Z F J (top d) r n (P v) (idempotent R.family _ v)).trans (equal v).symm
  change (h:ℂ)^d • P ((T h d).symm O)=D ((radius r (n+1):ℂ)^d • P ((T (radius r (n+1)) d).symm O))
  rw [ns,D.map_smul,old]
  change (h:ℂ)^d • grade R.family (top d) (Pert.Scale.gear R.family.labels d half.val (U v))=(((t*h:ℝ):ℂ)^d) • D (P v)
  rw [engineering,take,smul_smul,Complex.ofReal_mul,mul_pow,mul_comm ((t:ℂ)^d)];rfl

end YM.Integration.WilsonPositionScaleLawFixed
end
