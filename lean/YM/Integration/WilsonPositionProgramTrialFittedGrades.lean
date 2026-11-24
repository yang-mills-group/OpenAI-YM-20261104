import YM.Integration.WilsonPositionProgramTrialFittedHead

/-! Engineering factors and all signed graded heads of the actual zero-order thermal transfer. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedGrades
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialFittedTable (head)
open scoped BigOperators Classical

variable {G:Gauge}{h e:ℕ}
def Graded (F:Frame G h)(x:ℝ)(P:Wall F):Prop:=
  ∀i j,weight F i ≤ weight F j → P i j=if i=j then x^(h-weight F j) else 0

private theorem product {F:Frame G h}{x y:ℝ}{P Q:Wall F}(hp:Graded F x P)(hq:Graded F y Q):
    Graded F (x*y) (P*Q):=by
  intro i j old
  rw [Matrix.mul_apply,Finset.sum_eq_single i]
  · rw [hp i i le_rfl,if_pos rfl,hq i j old]
    by_cases eq:i=j <;> simp [eq,mul_pow]
  · intro b _ bi
    by_cases early:weight F i ≤ weight F b
    · rw [hp i b early,if_neg bi.symm,zero_mul]
    have bj:b≠j:=fun e=>early (e▸old)
    rw [hq b j ((not_le.mp early).le.trans old),if_neg bj,mul_zero]
  · simp

private theorem one {F:Frame G h}:Graded F 1 (identum (1:Wall F)):=by
  intro i j _
  by_cases eq:i=j <;> simp [identum,Matrix.one_apply,eq]

private theorem first {F:Frame G h}{s:Side}{P:Wall F}(lease:leaseM s F P):
    Graded F s.val (identum P):=by
  intro i j order
  by_cases val:valence F i=valence F j
  · simpa [identum,val,matPow] using lease.2 i j val order
  have different:i≠j:=fun eq=>val (eq▸rfl)
  simp [identum,val,different]

def scale (L:Levels G)(m:ℕ):ℕ→ℝ
  | 0=>1
  | k+1=>((loose L m).L.val:ℝ)*scale L (m+1) k
termination_by k=>k

theorem original (H:Hol G)(Q:SealR G){E W:Credit}(T:Theatre H Q.ans Q.path e E W)
    (N m k:ℕ)(paid:T.V.anchor ≤ m)(cut:m+k ≤ N):
    let L:=T.V.draws
    Graded Q.F (scale L m k) (identum (forwardW L T.V.paid Q.ans Q.path N m k)):=by
  intro L
  induction k generalizing m with
  | zero =>
    have home:forwardW L T.V.paid Q.ans Q.path N m 0=1:=by unfold forwardW CurNames; rw [hillcrest]; exact junior
    rw [home,scale];exact one
  | succ k ih =>
    have late:T.V.anchor ≤ m+1:=by omega
    have bound:m+1+k ≤ N:=by omega
    have A:=leaseN T (N:=N) paid (show m<N by omega)
    have B:=(wallways T late bound).2.1
    rw [fPace,identT A.1 B,scale]
    exact product (first A) (ih (m+1) late bound)

end YM.Integration.WilsonPositionProgramTrialFittedGrades
