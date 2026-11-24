import YM.Integration.WilsonOriginalStarFlagPrice
import YM.Integration.WilsonRootedKioskSlipCharge

/-! The exact signed reporting correction as a native hard-merger input.
The covering cost is independent of the period and is charged at each actual
root, before changing the marker radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalStarFlagMerger
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal Earn Sunrise
open Push Push.Corrected Push.AbsoluteSums Push.Local Animals MeasureTheory
open PhysicalNext.Repeat.Legato Extra.Trajectories ActualRunPhysicalPages
open WilsonOriginalStarFlagPrice WilsonOriginalStarSceneRows
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V] (d:V→ℕ)
  (N p k:ℕ) (v:(j:V)→R.family.label (d j)) (o:V→Site (R.family.side k p))
local notation "P" => R.family.path.rep N p k
local notation "D" j:max => (R.family.localSection (d j)).footprint (o j)
local notation "H" j:max => neighbors ((P).p.B+1) (o j)
local notation "S" j:max => kernel R N p k (d j) ((R.family.labels.level (d j)).core (v j)) (o j)
local notation "F" j:max => slip R d N p k v o j
local notation "J" => Stock.census V

private theorem widen {n:Side} {s t:Support n} {χ:ℝ} {f:Config G n→ℂ}
    (small:s ⊆ t) (fund:UsesFinal χ s f) : UsesFinal χ t f:=by
  intro u w same flags
  refine fund u w (agrees_mono same small) ?_
  have cut:=congrArg (fun y=>s ∩ y) flags
  simpa only [←Finset.inter_assoc,inter_eq_left.mpr small] using cut

omit [DecidableEq V] in
private theorem lawful (top:k≤N) (refs:∀i,R.family.ref (d i)≤k) (aperture:extent R d≤(P).p.B) (j:V) :
    GaugeInvariant (F j) ∧ Measurable (F j) ∧ UsesFinal (P).p.threshold (H j) (F j):=by
  let f := S j
  let s:=D j
  let h:=H j
  have reg:=(priced R N p k (d j) top (refs j) ((R.family.labels.level (d j)).core (v j)) (o j)).1
  have inHull : s⊆h:=contained R d o (P).p.B aperture j
  have outer:LocalOn h f:=fun U W agree=>reg.sites U W (agrees_mono agree inHull)
  have form : F j = fun U=>masked (P).p.threshold s f U - masked (P).p.threshold h f U:=by
    funext U
    exact eq_sub_of_add_eq' (posted R d N p k v o j aperture U)
  rw [form]
  exact ⟨fun z U=>congrArg₂ (·-·) (invariant_mask reg.symmetry _ s z U) (invariant_mask reg.symmetry _ h z U),
    (masked_measurable _ s f reg.borel).sub (masked_measurable _ h f reg.borel),
    fun U W same flags=>congrArg₂ (·-·) (widen inHull (uses_mask _ reg.sites) U W same flags)
      (uses_mask _ outer U W same flags)⟩

def sheet (top : k ≤ N) (refs : ∀i, R.family.ref (d i) ≤ k)
  (aperture : extent R d ≤ (R.family.path.rep N p k).p.B) (t : V → T → ℂ) : Canopy.ShiftRows T V G (P).p o J where
  place j:=⟨H j,⟨o j,(neighbors_mem ..).mpr (by simp)⟩⟩
  soap x j U:=Poly.send ((J).fire j) (t j x*(F j) U)
  cost x j:=by
    obtain ⟨g,m,uses⟩:=lawful R d N p k v o top refs aperture j
    let C : ℂ →ₗ[ℂ] Poly J := {
      toFun := Poly.send ((J).fire j)
      map_add' := send_add _
      map_smul' := by
        intro a b
        change Poly.send _ (a*b)=a • Poly.send _ b
        ext u
        rw [Poly.part_smul,Poly.part_send,Poly.part_send]
        split <;> simp }
    refine ⟨fun z U=>congrArg C (congrArg (fun l=>t j x*l) (g z U)),
      C.toContinuousLinearMap.continuous.measurable.comp (measurable_const.mul m),
      fun U W uv flags=>congrArg C (congrArg (fun l=>t j x*l) (uses U W uv flags)),
      fun U r live i hit=>?_⟩
    change (Poly.send _ _).part r≠0 at live
    rw [Poly.part_send] at live
    split at live
    next eq=>
      subst r
      have ij:i=j:=mem_singleton.mp hit
      subst i
      exact (neighbors_mem ..).mpr (by simp)
    next=>contradiction
  clean x j U h clean:=by
    apply h
    have zero:(F j) U=0:=if_neg (fun hs=>hs.2 clean)
    simp only [zero,mul_zero,Poly.send_zero]
  skip x j U:=by rw [Poly.part_send,if_neg ((J).fire_hot j).symm]
  single x j U:=by
    exact Classical.byContradiction fun h=> disjoint_left.mp ((merges_of_tagged_mul h).choose_spec.1) (mem_singleton_self j) (mem_singleton_self j)

variable (top : k ≤ N) (refs : ∀i, R.family.ref (d i) ≤ k)
  (aperture : extent R d ≤ (R.family.path.rep N p k).p.B) (t : V → T → ℂ)
local notation "M" => sheet R d N p k v o top refs aperture t
local notation "C" j:max => price R k (d j) ((R.family.labels.level (d j)).core (v j))

theorem charged (a:ℝ) (rate:0≤a) (w:V→ℝ) (rw0:∀i,0<w i) (ht:∀i x,‖t i x‖≤1) :
    (M).Budget w (P).p.B a (∑i:V,w i*(C i)*Real.exp (a*625)):=by
  let Y (i:V):=Poly.send ((J).fire i) ((C i):ℂ)
  have nn (i:V):0≤C i:= (priced R N p k (d i) top (refs i) ((R.family.labels.level (d i)).core (v i)) (o i)).2.1
  have identity (i:V): Poly.price w (Y i)=w i*(C i):=by
    dsimp only [Y]
    rw [Poly.solo,Complex.norm_real,Real.norm_of_nonneg (nn i)]
    simp only [Poly.toll,Census.fire,prod_singleton]
  refine ⟨Y,fun i x U r=>?_,fun z=>?_⟩
  · change ‖(Poly.send _ _).part r‖≤(Y i |>.part r).re ∧ (Y i |>.part r).im=0
    dsimp only [Y]
    simp only [Poly.part_send]
    split_ifs
    · refine ⟨?_,rfl⟩
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (ht i x)).trans (size R d N p k v o i top (refs i) U)
    · simp
  · let l (i:V):=if z∈H i then Poly.price w (Y i)*Real.exp (a*coverNumber (P).p.B (H i)) else 0
    have pos (i:V):0≤l i:=by unfold l;split;exact mul_nonneg (Poly.nonnegative rw0 _) (Real.exp_pos _).le;exact le_rfl
    refine ⟨pos,Summable.of_finite,?_⟩
    change ∑'i,l i≤_
    rw [tsum_fintype]
    apply Finset.sum_le_sum
    intro i _
    unfold l
    rw [identity]
    split
    next =>
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (rw0 i).le (nn i))
      apply Real.exp_monotone
      apply mul_le_mul_of_nonneg_left _ rate
      have b0:= (P).p.B_pos
      exact_mod_cast (Corona.cover_mono (Corona.halo_mono (show (P).p.B+1≤2*(P).p.B from by omega)
        (Finset.Subset.refl _)) _).trans (Corona.tile (o i) 2 (P).p.B b0)
    next =>exact mul_nonneg (mul_nonneg (rw0 i).le (nn i)) (Real.exp_pos _).le

theorem heard (σ:ℝ) (x:T) (U:Config G (R.family.side k p)) :
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let bank:=rendered (rows R d o σ g (P).p.threshold v t) (P).p g
    bank.log x U + (M).log x U =∑j:V,Poly.send ((J).fire j) (t j x*(v j 0+masked (P).p.threshold (D j) (S j) U)):=by
  simpa only [Canopy.ShiftRows.log,sheet,tsum_fintype] using all_fields R d N p k v o t σ top aperture x U

end YM.Integration.WilsonOriginalStarFlagMerger
