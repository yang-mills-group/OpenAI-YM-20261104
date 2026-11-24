import YM.RG05Readout.Many.Run
import YM.RG05Readout.Many.Pick

/-! A true source heading of zero cap stays zero on every descendant cell.
The full ward at any later date can therefore reopen its earlier admitted
census on every mode disjoint from the actual source shadow. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperShadow
open Function Set Finset Lattice Extra.Histories Push Marker RG05Readout
open RG05Readout.Address RG05Readout.Native RG05Readout.Many
open scoped Classical
variable {G:Gauge}{C:Family G}{n m t per:ℕ}{I:Type}
variable (o:I→Site (C.side n per))(E:I→Motion)(s:I→ℕ)(q:ManyStem C o n→Body)
local notation "A" => Mine.tree o E
local notation "F" => headings o E q

theorem inherited (nm:n ≤ m)(mt:m ≤ t)(z:ManyStem C o t)
    (dead:Mine.shelter o nm mt z∈shadow A s F m): z∈shadow A s F t := by
  induction mt with
  | refl => simpa only [Mine.vanishDepth] using dead
  | step hi ih =>
    rename_i i
    let ni:=nm.trans hi
    let y:=((A).narrows i ni z).1
    have past:Mine.shelter o nm hi y∈shadow A s F m:=by
      simpa only [Mine.spec_grow o E nm hi z,y,ni] using dead
    have quiet:=ih y past
    change Cap (s ((A).labelY (i+1) z)+2) ((F) (i+1) z) 0
    rw [(headlines (N:=i+1) o E q).2 i ni (Nat.lt_succ_self i) z,(A).loyal i ni z]
    have one:1≤((C.S.block i).val:ℝ):=by exact_mod_cast (C.S.block i).property
    exact cap_aff _ (by positivity) (inv_le_one_of_one_le₀ one) (Address.dist_box ..) quiet

theorem restored [DecidableEq I] [Fintype I] (roster:Census I) (nm:n ≤ m)(mt:m ≤ t)
    (clear:Clearance o E s F roster m)(z:(Mine.ward o E roster t).Mode)
    (alive:Disjoint (shadow A s F t) (z.val:Set _)):
    z.val∈(Mine.masts o E nm (barren o E roster m) t).choices := by
  let u:=Mine.shelter o nm mt
  let w:=z.val.image u
  have enrolled:Lit roster ((A).labelY t) z.val:=(mem_filter.mp z.property).2
  have color:(A).labelY m ∘ u=(A).labelY t:=rfl
  have read:Lit roster ((A).labelY m) w:=by
    refine ⟨?_,?_⟩
    · change (z.val.image u).image ((A).labelY m) ∈ roster.choices
      rw [Finset.image_image,color]; exact enrolled.1
    · intro a ha b hb eq
      obtain ⟨i,hi,rfl⟩:=mem_image.mp ha
      obtain ⟨j,hj,rfl⟩:=mem_image.mp hb
      exact congrArg u (enrolled.2 hi hj eq)
  have parent:w∈(Mine.ward o E roster m).choices:=mem_filter.mpr ⟨mem_univ _,read⟩
  have old:Disjoint (shadow A s F m) (w:Set _):=by
    apply Set.disjoint_left.mpr
    intro j dead seen
    obtain ⟨i,hi,rfl⟩:=mem_image.mp seen
    exact Set.disjoint_left.mp alive (inherited o E s q nm mt i dead) hi
  have collected:w∈(barren o E roster m).choices:=mem_filter.mpr ⟨parent,clear ⟨w,parent⟩ old⟩
  unfold Mine.masts
  rw [dif_pos mt]
  apply mem_filter.mpr
  refine ⟨mem_univ _,collected,?_⟩
  intro i hi j hj eq
  exact enrolled.2 hi hj (congrArg ((A).labelY m) eq)

end YM.Integration.WilsonReportHarvestUpperShadow
