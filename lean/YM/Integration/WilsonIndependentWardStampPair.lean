import YM.Integration.WilsonIndependentRawNamedOrbit

/-! A paid relative-position opening for two fixed cover stencils on the
same enrolled notebook. Their ordinary product keeps all scalar feeds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardStampPair
open Lattice RG RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Uniform RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Cluster.Collapsed
open WilsonIndependentRawWordGeometry
open RegulatorIR.Prim RegulatorIR.Taping RegulatorIR.Motion
open scoped Classical ENNReal NNReal BigOperators
variable {G:Gauge}{m n:ℕ}{B C:Portrait G}

def bank (A:LocalStamp B m) : Orders (Foot G) := (stamp_symbol A).choose
def moved (A:LocalStamp B m)(o:Cover) : Orders (Foot G) :=
  fun i r=>echo (carryX o) (bank A i r)

theorem placed (A:LocalStamp B m)(o:Cover) :
    BasisT m m (convey o B) (moved A o) ∧ Ranks m (moved A o) := by
  obtain ⟨H,N⟩:=(stamp_symbol A).choose_spec
  refine ⟨H.vayne o,?_⟩
  intro i j alive
  apply N i j
  intro dead
  exact alive ((congrArg (echo (carryX o)) dead).trans echo_zero)

variable (A:LocalStamp B m)(A':LocalStamp C n)
def ranks (o z:Cover) : Orders (Foot G) := accord (moved A o) (moved A' z)

theorem issued (o z:Cover) :
    BasisT (m+n) (m+n) (convey o B*convey z C) (ranks A A' o z) ∧
    Ranks (m+n) (ranks A A' o z) :=
  ⟨Profiles.BasisT.united (placed A o).1 (placed A' z).1 (placed A o).2 (placed A' z).2,
    rank_pair (placed A o).2 (placed A' z).2⟩

def price (u i r:ℕ) : ℝ≥0∞ :=
  ∑j ∈ (_root_.Finset.HasAntidiagonal.antidiagonal i : Finset (ℕ×ℕ)),
    ∑ v ∈ (_root_.Finset.HasAntidiagonal.antidiagonal r : Finset (ℕ×ℕ)),
    markQ (root 0 (u+u)) (bank A j.1 v.1)*markQ (root 0 (u+u)) (bank A' j.2 v.2)

theorem paid (u i r:ℕ) : price A A' u i r≠⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j _
  apply ENNReal.sum_ne_top.mpr
  intro v _
  exact ENNReal.mul_ne_top (finite _ _ ((stamp_symbol A).choose_spec.1.canopy _ _)) (by exact finite _ _ ((stamp_symbol A').choose_spec.1.canopy _ _))

theorem rooted (u i r:ℕ)(o z:Cover)(x:Room) :
    markQ (root x u) (ranks A A' o z i r) ≤
      price A A' u i r * WilsonIndependentRawPairBudget.reach x o z u := by
  apply (joined_root x u _).trans
  unfold ranks accord price
  apply (quota_sum ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  unfold crisp
  apply (quota_sum ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v hv
  have eqn:=_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  rw [←eqn,pie,dif_pos rfl]
  apply (packet_pair zero_lt_one (u+u) {x} (localL (G:=G) 1) _ _).trans
  apply (mul_le_mul' (recenter x _ (bank A j.1 v.1) o)
    (recenter x _ (bank A' j.2 v.2) z)).trans_eq
  unfold WilsonIndependentRawPairBudget.reach
  ring

variable {I:Type}{M:I→ℕ}{side:Page M→Side}{S:Heir side G}(V:Reel S)
  (T:S.Accounts)(L:Meter I)(x:I → Room)(o z:I → Cover)

def report : T.Report (m+n) := declaring T (fun i=>ranks A A' (o i) (z i))
  (fun i=>(issued A A' (o i) (z i)).2)

include V in
theorem opening (p u:ℕ)(start:∀ w,S.l (Page.opening M w)=1)
    (budget:∀ w,ENNReal.ofReal (1+WilsonIndependentRawPairOpening.span x o z w)≤L.val w) :
    WilsonIndependentRawWordTransport.Opening (p:=p) (x:=x) (u:=u) (L:=L)
      (report A A' T o z) (wage:=1) := by
  intro i _ r
  apply Carry.regular
  refine ⟨_,(u+u)+(u+u),paid A A' u i r,?_⟩
  intro w
  change markQ (S.coverQ x u (Page.opening M w)) (ranks A A' (o w) (z w) i r) ≤ _
  rw [WilsonIndependentRawPairOpening.seated V x start w u r]
  apply (rooted A A' u i r (o w) (z w) (x w)).trans
  apply mul_le_mul_right
  rw [pow_add]
  unfold WilsonIndependentRawPairBudget.reach displacement Tariff.amount
  simp only [div_one]
  apply mul_le_mul'
  · apply pow_le_pow_left'
    apply (ENNReal.ofReal_le_ofReal (q:=1+WilsonIndependentRawPairOpening.span x o z w) _).trans (budget w)
    unfold WilsonIndependentRawPairOpening.span
    linarith [show 0≤dist (x w) (slide 1 (z w)) from dist_nonneg]
  · apply pow_le_pow_left'
    apply (ENNReal.ofReal_le_ofReal (q:=1+WilsonIndependentRawPairOpening.span x o z w) _).trans (budget w)
    unfold WilsonIndependentRawPairOpening.span
    linarith [show 0≤dist (x w) (slide 1 (o w)) from dist_nonneg]

end YM.Integration.WilsonIndependentWardStampPair
