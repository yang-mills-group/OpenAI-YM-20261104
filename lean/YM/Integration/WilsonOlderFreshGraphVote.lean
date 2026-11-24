import YM.Integration.WilsonOlderFreshGraphAward
import YM.QuadraticLocal.Campaign.Stencil

/-! A paid publication is a literal before-test physical voter. All its
genuine nonzero atoms share the submitted physical binder. Zero-magnitude
atoms have vanishing group functions on every field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphVote
open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open scoped Classical BigOperators Topology

variable {G:Gauge}{n:Side}{Q d:ℕ}{α:Type}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit) (C:Fin (Q+1)→ℝ) (σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest) (d0:0<d) (weight:α→ℂ)

abbrev Name := (j:Fin (Q+1)) × {u:(W j).Ty // 0<((W j).leg u).atom.magnitude}

def material (z:Name W) : Earn.Row P H G α:=
  WilsonOlderFreshGraphMount.ballot S ((W z.1).leg z.2.1) z.1 d d0
    ((paid z.1).pinned z.2.1) (legal z.1 z.2.1) z.2.2 σ weight

local notation "M"=>material S W C σ paid legal d0 weight

theorem factor {j:Fin (Q+1)} {u:(W j).Ty} (absent:¬0<((W j).leg u).atom.magnitude)
    (U:Config G n) (y:Site n):
    ((W j).leg u).atom.unmasked U y=0:=
  Bloom.awaken _ U y (le_antisymm (le_of_not_gt absent) (Texture.mag_nonneg _))

theorem voter (cap:∀t,‖weight t‖≤1) {order seats stage vac shelf:ℕ} (seats1:1≤ seats)
    (launch:order+1≤ stage) (budget:order+d≤Burn.horizon vac+2) (qfit:Q≤ shelf) (high:d≤ shelf):
    Cruise.Voter M σ order seats stage vac shelf := by
  have single:S.mode.val=univ:=by
    apply Finset.eq_univ_of_forall
    intro v
    have hv:v=S.front:=Subsingleton.elim _ _
    exact hv ▸ S.east
  have due (z:Name W): (M z).Credentials Q (fun _=>d):=by
    change z.1.val ≤ Q ∧ d=∑ v∈S.mode.val,d
    exact ⟨Nat.le_of_lt_succ z.1.isLt,by simp [single]⟩
  refine ⟨fun z=>?_,fun i=>?_,launch,fun club=>?_⟩
  · have earned:=WilsonOlderFreshGraphMount.enrolled S ((W z.1).leg z.2.1) z.1 d d0
      ((paid z.1).pinned z.2.1) (legal z.1 z.2.1) z.2.2 σ weight cap
    exact ⟨earned.1,earned.2.1,(Nat.le_of_lt_succ z.1.isLt).trans qfit,high⟩
  · exact (Finset.card_le_univ i.val).trans (by simpa using seats1)
  · rw [Press.tall M club (fun _=>d) due]
    have h:(∑ _i∈(Club.alliance M club).val,d) ≤ ∑ _i:Unit,d:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
    simpa using (Nat.add_le_add_left h order).trans (by simpa using budget)

theorem before_tests (σ0:0≤σ):
    SumBudget (fun z:Name W=>(M z).height σ) (Real.exp (σ*S.length)*(∑j,C j)) := by
  have cost (j:Fin (Q+1)):SumBudget (fun z:{u:(W j).Ty//0<((W j).leg u).atom.magnitude} =>
      (M ⟨j,z⟩).height σ) (Real.exp (σ*S.length)*C j):=by
    have hand:=budget_scale (Real.exp_pos (σ*S.length)).le
      (budget_pull (fun z:{u:(W j).Ty//0<((W j).leg u).atom.magnitude}=>z.val)
        (Subtype.val_injective) (paid j).price)
    apply Local.sumBudget_mono hand (fun z=>mul_nonneg (M ⟨j,z⟩).sound.le (Real.exp_pos _).le) (fun z=>?_) le_rfl
    · exact WilsonOlderFreshGraphMount.hearing S ((W j).leg z.1) j d d0
        ((paid j).pinned z.1) (legal j z.1) z.2 σ weight le_rfl σ0
  apply Push.Local.sumBudget_sigma cost
  rw [Finset.mul_sum]
  exact budget_finite (fun j=>mul_nonneg (Real.exp_pos _).le (budget_nonneg (paid j).price)) le_rfl

end YM.Integration.WilsonOlderFreshGraphVote
end
