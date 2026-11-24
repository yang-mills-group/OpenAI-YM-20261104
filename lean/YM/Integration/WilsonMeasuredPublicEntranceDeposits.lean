import YM.Integration.ActualWilsonAbsoluteTransport

/-! Each occupied face of the true upper Wilson portfolio retains its
conditional deposits at every intervening scale. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceDeposits
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){p k:ℕ}(N:ℕ)
local notation "X" i:max => Config G ((C).side i p)
def funded {Space:Type*}[MeasurableSpace Space](a:Space → ℂ):Prop:=Measurable a ∧ ∃M:ℝ,∀U,‖a U‖ ≤ M

def mean {k:ℕ}(A:X k → ℂ)(i:ℕ):X i → ℂ:=if h:i ≤ k then actualTransport C (N:=N) A h else 0

theorem salary {A:X k → ℂ}(hC:C.Makes)(paid:funded A)(live:k ≤ N){i:ℕ}(before:i ≤ k):
    ∃M:ℝ,AEStronglyMeasurable (mean C N A i) (prior G _) ∧ ∀U,‖mean C N A i U‖ ≤ M:=by
  obtain ⟨borel,M,bound⟩:=paid
  rw [mean,dif_pos before]
  exact ⟨M,(actualTransport_integrable C hC live borel.aestronglyMeasurable bound before).aestronglyMeasurable,
    actualTransport_norm_le C hC live bound before⟩

variable {I:Type} (A:I → Config G (C.side k p) → ℂ)(s:Finset I)

def singles (i:ℕ)(U:X i):ℂ:=∏a∈s,mean C N (A a) i U

def deposit (i:ℕ)(U:X i):ℂ:=
  actualTransport (C) (N:=N) (singles C N A s (i+1)) (Nat.le_succ i) U - singles C N A s i U

def reading (f i:ℕ)(W:X f):ℂ:=if h:f ≤  i then actualTransport (C) (N:=N) (deposit C N A s i) h W else 0

theorem integrable (hC:C.Makes)(fund:∀a,funded (A a))(live:k ≤ N){i:ℕ}(before:i ≤ k):
    Integrable (fun U=>((C).path.rep N p i).eval U • singles C N A s i U) (prior G _):=by
  choose M borel bound using fun a=>salary C N hC (fund a) live before
  have good:AEStronglyMeasurable (singles C N A s i) (prior G _):=
    s.aestronglyMeasurable_fun_prod (fun a _=>borel a)
  have cap (U:X i):‖singles C N A s i U‖  ≤  ∏a∈s,M a:=by
    rw [singles,norm_prod]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>bound a U)
  have cost:=actualTransport_weighted_integrable (C) hC (before.trans live) good cap (le_refl i)
  rwa [actualTransport_base (C) hC (before.trans live)] at cost

theorem window (hC:C.Makes)(fund:∀a,funded (A a))(live:k ≤ N){f K:ℕ}(first:f ≤ K)(last:K ≤ k)(W:X f):
    actualTransport (C) (N:=N) (fun U=>∏a∈s,A a U) (first.trans last) W - actualTransport C (N:=N) (singles C N A s K) first W =
      ∑i∈Ico K k,reading C N A s f i W:=by
  have earlier:=first.trans last
  let stage (i:ℕ):ℂ:=if h:f ≤  i then actualTransport (C) (N:=N) (singles C N A s i) h W else 0
  have bottom:stage K=actualTransport C (N:=N) (singles C N A s K) first W:=dif_pos first
  have top:stage k=actualTransport (C) (N:=N) (fun U=>∏a∈s,A a U) earlier W:=by
    have last:singles C N A s k = fun U=>∏a∈s,A a U:=by
      funext U
      simp only [singles,mean,dif_pos le_rfl,actualTransport_base (C) hC live]
    simp only [stage,dif_pos earlier,last]
  have sum:(∑i∈Ico K k,reading C N A s f i W)=∑i∈Ico K k,(stage (i+1)-stage i):=by
    apply sum_congr rfl
    intro i hi
    obtain ⟨lower,lt⟩:=mem_Ico.mp hi
    have lo:=first.trans lower
    have late:i+1 ≤ k:=lt
    have upper:=integrable C N A s hC fund live late
    have lower:=integrable C N A s hC fund live ((Nat.le_succ i).trans late)
    have bought:=actualTransport_weighted_integrable_of_integrable (C) hC (late.trans live) upper (Nat.le_succ i)
    simp only [reading,dif_pos lo,stage,dif_pos (lo.trans (Nat.le_succ i))]
    have difference:=congrFun (ActualWilsonAbsoluteTransport.sub (C) hC (((Nat.le_succ i).trans late).trans live) bought lower lo) W
    exact difference.trans (congrArg (fun x=>x-_) (congrFun (actualTransport_tower (C) hC (late.trans live) (singles C N A s (i+1)) (Nat.le_succ i) lo) W))
  rw [sum,sum_Ico_eq_sub _ last]
  simp_rw [sum_range_sub]
  rw [top,bottom]
  abel

theorem original (hC:C.Makes)(fund:∀a,funded (A a))(live:k ≤ N){f:ℕ}(earlier:f ≤ k)(W:X f):
    actualTransport C (N:=N) (fun U=>∏a∈s,A a U) earlier W - singles C N A s f W =
      ∑i∈Ico f k,reading C N A s f i W:=by
  simpa only [actualTransport_base C hC (earlier.trans live)] using
    window C N A s hC fund live (le_refl f) earlier W

end YM.Integration.WilsonMeasuredPublicEntranceDeposits
end
