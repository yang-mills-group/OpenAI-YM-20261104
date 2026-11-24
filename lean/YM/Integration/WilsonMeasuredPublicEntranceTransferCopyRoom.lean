import YM.Integration.WilsonMeasuredPublicEntranceTransferSubmittedPhase
/-! Before either ultraviolet regulator the complete signed test and all its interpolating cells fit in one true reflected-copy chamber. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 850000
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRoom
open Function Filter Set Finset MeasureTheory Metric Lattice Wilson RG Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Therm OPE.Therm.ReplicaChessboard
open WilsonMeasuredPublicEntranceTransferSubmittedPhase (site)
open WilsonMeasuredPublicEntranceBookedSurvey (Press owned)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "A₀" => (C₀).path.levels

def reach (f:ℕ)(radius:ℝ):ℕ:=⌈radius/(C₀).S.a f⌉₊

theorem at_site {f K n p:ℕ}(fk:f≤K)(d:Fin n→ℕ)(S:ℕ)(st:∀i,stencilRadius (C₀) (d i)≤S)
    (o:Fin n→ Cover)(radius:ℝ)(bound:∀i,‖(C₀).S.gridPoint f (o i)‖≤radius):
    ∀i,window (site (R:=R) (p:=p) fk o i) (stencilRadius (C₀) (d i))⊆
      window 0 (((C₀).S.toDepth fk p).count.val*reach R f radius+S):=by
  intro i U hu
  let a:=((C₀).S.toDepth fk p)
  have on_f:wrap ((C₀).side f p) (o i)∈window 0 (reach R f radius):=by
    refine ⟨o i,?_,by simp⟩
    change o i∈box _
    rw [box_test]
    have coord(t:Axis):|(o i t:ℝ)|≤(reach R f radius:ℝ):=by
      have where_:= (PiLp.norm_apply_le ((C₀).S.gridPoint f (o i)) t).trans (bound i)
      change |(C₀).S.a f*(o i t:ℝ)|≤radius at where_
      rw [abs_mul,abs_of_pos ((C₀).S.a_pos f)] at where_
      exact ((le_div_iff₀ ((C₀).S.a_pos f)).mpr (by simpa only [mul_comm] using where_)).trans (Nat.le_ceil _)
    constructor
    · intro t;exact_mod_cast (abs_le.mp (coord t)).1
    · intro t;exact_mod_cast (abs_le.mp (coord t)).2
  have atK:=window_embed a on_f
  rw [←Ratio.root_embed,map_zero] at atK
  apply window_add atK
  obtain ⟨z,hz,h⟩:=hu
  exact ⟨z,box_larger hz (st i),h⟩

theorem original (J S:ℕ)(M:ℝ):
    ∃ε:ℝ,0<ε ∧ ∃floor:ℕ,∀{f K n p:ℕ}(fk:f≤K),floor≤f → ∀{r:ℝ},0<r → r<ε →
    let size:=((C₀).S.toDepth fk p).count.val*reach R f ((|M+1|+1)*r)+S
    room (A₀) J K size ∧ ∀d:Fin n→ℕ,(∀i,stencilRadius (C₀) (d i)≤S) →
      ∀o:Fin n→ Cover,(∀i,‖(C₀).S.gridPoint f (o i)‖≤(M+1)*r) →
      ∀i,window (site (R:=R) (p:=p) fk o i) (stencilRadius (C₀) (d i))⊆window 0 size:=by
  let a:=(C₀).S.a J
  let C:=|M+1|+1
  have ap:0<a:=(C₀).S.a_pos _
  have cp:0<C:=by dsimp [C];positivity
  let e:=a/(8*C)
  have ep:0<e:=div_pos ap (mul_pos (by norm_num) cp)
  have vanishes:Tendsto (fun k=>(C₀).S.a k*(S+1:ℝ)+tail (A₀) k) atTop (𝓝 0):=by
    simpa using (((C₀).S.shrinks.mul_const (S+1:ℝ)).add (tail_zero (A₀)))
  have late:=vanishes.eventually (gt_mem_nhds (show 0<a/8 by positivity))
  obtain ⟨floor,withFee⟩:=eventually_atTop.mp late
  refine ⟨e,ep,floor,?_⟩
  intro f K n p fk passed r rp small size
  have uf:=withFee f passed
  have uk:=withFee K (passed.trans fk)
  have af:0<(C₀).S.a f:=(C₀).S.a_pos _
  have ak:0<(C₀).S.a K:=(C₀).S.a_pos _
  have edge:(C₀).S.a f*reach R f (C*r)<C*r+(C₀).S.a f:=by
    have v:=mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg cp.le rp.le) af.le)) af
    have eq:(C₀).S.a f*(C*r/(C₀).S.a f)=C*r:=by field_simp
    simpa only [reach,mul_add,mul_one,eq] using v
  have physical:C*r<a/8:=by
    have paid:=(lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) cp)).mp small
    nlinarith
  have base:(C₀).S.a f<a/8:=by
    have ht:=tail_pos (A₀) f
    have hs:0≤(C₀).S.a f*(S:ℝ):=mul_nonneg af.le (Nat.cast_nonneg _)
    nlinarith
  constructor
  · have scale:(C₀).S.a K*(size:ℝ)=(C₀).S.a f*(reach R f (C*r):ℝ)+(C₀).S.a K*(S:ℝ):=by
      dsimp only [size]
      rw [Nat.cast_add,Nat.cast_mul,mul_add,←mul_assoc,(C₀).S.embeds_scale ((C₀).S.toDepth fk p)]
    change 2*((C₀).S.a K*(size:ℝ)+tail (A₀) K)<a
    rw [scale]
    nlinarith
  · intro d st o where_
    apply at_site R fk d S st o (C*r)
    intro i
    apply (where_ i).trans
    exact mul_le_mul_of_nonneg_right ((le_abs_self (M+1)).trans (by dsimp [C];linarith)) rp.le

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRoom
end
