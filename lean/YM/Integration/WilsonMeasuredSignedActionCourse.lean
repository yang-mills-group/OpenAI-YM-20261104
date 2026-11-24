import YM.Integration.WilsonMeasuredSignedActionRestart
import YM.Integration.WilsonMeasuredSignedActionCone
import YM.Integration.WilsonMeasuredPublicEntranceActionInvariant
import YM.Integration.WilsonPositionProgramBlockedTrialCone

/-! Signed return of a compact K-born column on the elected N-vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionCourse
open Function Filter Finset Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor MergeProof Campaign Bid
open scoped Classical BigOperators Topology
variable {G:Gauge}

def fixed (F:Frame G 4)(v:F.Coeff):Prop:=∀y:Motion,Motion.patch F y v=v
def axis (F:Frame G 4):F.Coeff:=F.core (F.coords (Trace.square4 G))
def positive (F:Frame G 4)(v:F.Coeff):Prop:=
  ∃s:ℝ,0<s ∧ F.core v=(s:ℂ) • axis F

theorem read {F:Frame G 4}(simple:G.Simple){v:F.Coeff}(held:fixed F v):
    ∃s:ℝ,F.core v=(s:ℂ) • axis F:=by
  have rot:∀s:Signed,F.act s.ortho v=v:=fun s=>held (s,false)
  have real:star v=v:=by
    simpa only [Motion.patch,if_true,show (1:Signed).ortho=1 from map_one Signed.inclusionO,
      Frame.act_one] using held (1,true)
  obtain ⟨u,s,h⟩:=WilsonMeasuredPublicEntranceActionInvariant.coordinates simple F v (congrFun real) rot
  refine ⟨s,?_⟩
  rw [h];funext i
  by_cases isUnit:i=0
  · subst i;simp [axis,Frame.core]
  · simp [axis,Frame.core,isUnit,Frame.e0,Complex.real_smul]

private theorem cost_zero (F:Frame G 4){z:F.Coeff}(h:¬0<F.coeffSize z):z=0:=by
  funext i
  apply norm_eq_zero.mp
  exact le_antisymm ((Finset.single_le_sum (f:=fun t=>‖z t‖) (fun t _=>norm_nonneg _) (Finset.mem_univ i)).trans (le_of_not_gt h)) (norm_nonneg _)

variable (R:Run G){T:Campaign R}(L:Pillars R T)
local notation "F₀" => R.family.labels.level 4
local notation "C₀" => R.family
local notation "B₀" => R.family.localSection 4
local notation "H₀" => R.family.path
local notation "P₀" => R.family.params

include L in
private theorem carry (simple:G.Simple){N per b:ℕ}(bought:R.t 4≤b)
    (reserve:∀j,b≤j→ barunit (R.family.S.block j) <
      (((H₀).levels.budget j).threshold/((H₀).levels.budget (j+1)).threshold)^2)
    (n:ℕ)(live:b+n≤N)(V:Voice F₀ H₀ per (b+n))
    (hv:Heard B₀ H₀ N per P₀ (b+n) V)(chor:Chorus H₀ N per (b+n) V):
    ∃Z:Voice F₀ H₀ per b,Heard B₀ H₀ N per P₀ b Z ∧ Chorus H₀ N per b Z ∧
      (∀v,flow C₀ 4 N per b n ((V.plays v).density 0 B₀ ((H₀).rep N per (b+n)))=
        (Z.plays v).density 0 B₀ ((H₀).rep N per b)) ∧
      ∀v,fixed F₀ v→positive F₀ (V.index v)→positive F₀ (Z.index v):=by
  induction n with
  | zero=>exact ⟨V,hv,chor,fun _=>rfl,fun _ _ h=>h⟩
  | succ n ih=>
    have age:b+n<N:=by omega
    obtain ⟨U,Q,heading,heard,returned,closed,step⟩:=
      WilsonMeasuredSignedActionRestart.edge R L simple (bought.trans (by omega)) age V hv chor
    obtain ⟨Z,hz,cz,back,sign⟩:=ih age.le Q heard closed
    refine ⟨Z,hz,cz,?_,?_⟩
    · intro v
      rw [flow]
      change flow C₀ 4 N per b n (blast H₀ N per (b+n) 4 _) = _
      exact (congrArg (flow C₀ 4 N per b n) (returned.values v).symm).trans (back v)
    · intro v hv0 upper
      apply sign v hv0
      obtain ⟨a,ap,xa⟩:=upper
      have fv:fixed F₀ (Q.index v):=fun y=>(heard.moves v y).trans (congrArg Q.index (hv0 y))
      obtain ⟨c,yc⟩:=read simple fv
      by_cases nonzero:0<(F₀).coeffSize (axis F₀)
      · exact ⟨c,WilsonMeasuredSignedActionCone.oriented F₀ simple U _ heading nonzero xa yc (step v)
          (reserve (b+n) (by omega)) ap,yc⟩
      · have zero:=cost_zero F₀ nonzero
        refine ⟨1,zero_lt_one,?_⟩
        simp [yc,zero]

include L in
theorem original (simple:G.Simple):∀ᶠ b:ℕ in atTop,∀{N per n:ℕ}(_live:b+n≤N)
    (V:Voice F₀ H₀ per (b+n))(_hv:Heard B₀ H₀ N per P₀ (b+n) V)
    (_chor:Chorus H₀ N per (b+n) V),∃Z:Voice F₀ H₀ per b,
      Heard B₀ H₀ N per P₀ b Z ∧ Chorus H₀ N per b Z ∧
      (∀v,flow C₀ 4 N per b n ((V.plays v).density 0 B₀ ((H₀).rep N per (b+n)))=
        (Z.plays v).density 0 B₀ ((H₀).rep N per b)) ∧
      ∀v,fixed F₀ v→positive F₀ (V.index v)→positive F₀ (Z.index v):=by
  obtain ⟨j,budget⟩:=eventually_atTop.mp (WilsonMeasuredSignedActionCone.affordable R simple)
  filter_upwards [eventually_ge_atTop (max j (R.t 4))] with b big
  intro N per n live V hv ch
  exact carry R L simple ((le_max_right ..).trans big)
    (fun k hk=>budget k (((le_max_left ..).trans big).trans hk)) n live V hv ch

end YM.Integration.WilsonMeasuredSignedActionCourse
end
