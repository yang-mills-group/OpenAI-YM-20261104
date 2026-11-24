import YM.Integration.WilsonOriginalPublicNodalUnitSeeds
import YM.Integration.WilsonPositionProgramTrialVisitDose

/-! The funded public input uses the same held value on every physical coefficient of one source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPlainSensor
open Function Finset Lattice RG Wilson Precision Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramSubmittedCoordinates (plain)
open WilsonPositionProgramTrialFittedTable (head)
open WilsonPositionProgramTrialFittedBudget (scalar)
open WilsonPositionProgramMasterBirth (rank)
open WilsonReceivedCanonicalSocketSeed (contact)
open scoped Classical BigOperators
variable {G:Gauge}{l D:ℕ}

theorem only (F:Frame G l)(s:Alma F)(ordinary:rankS s.val.2=0):s=plain F (sheet F s):=by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  exact Multiset.card_eq_zero.mp ordinary

def sensor (D:ℕ):Vote D:=claim D (contact D) zeroC

theorem chosen (F:Frame G l)(w:l<D)(b:F.Index):
    jewelBloom w (plain F b)=sensor D:=by
  unfold jewelBloom sensor
  apply congrArg (fun k:Knob D=>claim D k zeroC)
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  funext j
  exact Fin.elim0 (show Fin 0 from j)

theorem unit (D:ℕ):sensor D (page D (WilsonReceivedCanonicalSocketSeed.sheet D))=1:=by
  change claim D ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ zeroC (page _ (WilsonReceivedCanonicalSocketSeed.sheet _))=1
  rw [nib _ (Nat.zero_le _) Fin.elim0]
  simp [crease,WilsonReceivedCanonicalSocketSeed.sheet,iteratedFDeriv_zero_apply]

theorem compress (F:Frame G l){M:Type*}[AddCommMonoid M](f:Alma F→M)
    (vanish:∀s:Alma F,rankS s.val.2≠0→f s=0):
    ∑s,f s=∑b,f (plain F b):=by
  let live:=Finset.univ.filter (fun s:Alma F=>rankS s.val.2=0)
  calc
    ∑s,f s=∑s∈live,f s:=by
      apply (sum_subset (filter_subset ..) ?_).symm
      intro s _ absent
      apply vanish
      simpa [live] using absent
    _=∑b,f (plain F b):=by
      apply sum_bij' (fun s _=>sheet F s) (fun b _=>plain F b)
      · simp
      · intro b _
        simp [live,WilsonPositionProgramSubmittedCoordinates.plain,rankS]
      · intro s hs
        exact (only F s ((mem_filter.mp hs).2)).symm
      · intro b _
        rfl
      · intro s hs
        exact congrArg f (only F s ((mem_filter.mp hs).2))

theorem original (R:Run G)(w:l<D)(K:ℕ)(n:Side)
    (x:R.family.label l)(φ:ℂ →L[ℝ] ℝ)(b:Volume D):
    let F:=R.family.labels.level l
    let S:=R.family.localSection l
    let T:=Shrine (Peaks R.family.path.levels R.metals.O S w K K) (head (scalar x φ))
    PowerSeries.X^rank R (d:=l)*flash (jot b (T.1 n))=
      (sensor D b) • ∑i:F.Index,PowerSeries.X^(rank R (d:=l)-(F.grades i).2)*
        Blue.soil (PowerSeries.C (φ (x i)))*jet (Plies S i n):=by
  intro F S T
  rw [WilsonPositionProgramMasterBirth.assembly R w K n (head (scalar x φ)) b]
  refine (compress F _ ?_).trans ?_
  · intro s h
    change _*Blue.soil (PowerSeries.C (scalar x φ s))*_=_
    simp [scalar,h]
  · rw [Finset.smul_sum]
    apply sum_congr rfl
    intro i _
    rw [chosen]
    change _*(Blue.soil (PowerSeries.C (scalar x φ (plain F i))))*((sensor D b) • jet (Plies S i n))=_
    rw [show scalar x φ (plain F i)=φ (x i) from by simp [scalar,WilsonPositionProgramSubmittedCoordinates.plain,rankS]]
    rw [mul_smul_comm]
    rfl

end YM.Integration.WilsonOriginalPublicNodalPlainSensor
end
