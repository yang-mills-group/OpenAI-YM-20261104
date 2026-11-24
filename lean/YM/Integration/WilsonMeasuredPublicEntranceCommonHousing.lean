import YM.Integration.WilsonMeasuredPublicEntranceTwoHostEar
/-! The original pair housing at the common coarse reporter pays for the
actual finite ancestor roster used by both conditional Wilson readings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCommonHousing
open Function Finset Lattice Wilson RG QuadraticLocal Push.Local
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonOriginalOccupiedCorridor
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]{p f b:ℕ}
variable (o:V → Site (R.family.side f p))(path:∀j,(Unit×(V×Bool)) → Site (R.family.side j p))
omit [Fintype V][DecidableEq V] in
theorem carried (old:b ≤ f)(top:path f=(o∘Prod.fst)∘Prod.snd)
    (line:∀j,b ≤ j → j<f → path j=(R.family.path.levels.clock.op j p).ratio.parent ∘ path (j+1)) (t:Unit×(V×Bool)):
    sites R o old t.2.1=path b t:=by
  refine Nat.decreasingInduction (motive:=fun j jf=>b≤j → sites R o jf t.2.1=path j t) ?_ ?_ old le_rfl
  · intro j jf previous bj
    have stage:sites R o jf.le=(R.family.path.levels.clock.op j p).ratio.parent ∘ sites R o jf:=
      Nat.decreasingInduction_succ_left ..
    rw [stage,line j bj jf,Function.comp_apply,Function.comp_apply,previous (bj.trans (Nat.le_succ j))]
  · intro _
    rw [show sites R o (le_refl f)=o from Nat.decreasingInduction_self ..,top]
    rfl

omit [DecidableEq V] in
theorem original (old:b≤f)(top:path f=(o∘Prod.fst)∘Prod.snd)
    (line:∀j,b≤j → j<f → path j=(R.family.path.levels.clock.op j p).ratio.parent ∘ path (j+1))
    (anchor:Unit×(V×Bool))(B l:ℕ)(pairs:∀i:Unit×(V×Bool),coverNumber B ({path b anchor,path b i}:Support _)≤l):
    ∃Z:Support (R.family.side b p),path b anchor∈Z ∧ (∀v,sites R o old v∈Z) ∧
      coverNumber B Z≤l+Fintype.card V*l:=by
  let a:=path b anchor
  let piece(v:V):Support (R.family.side b p):={a,sites R o old v}
  let Z:Support (R.family.side b p):={a}∪Finset.univ.biUnion piece
  have costs(v:V):coverNumber B (piece v)≤l:=by
    have step:=carried R o path old top line ((),v,false)
    change coverNumber B ({a,sites R o old v}:Support _)≤l
    rw [show sites R o old v=path b ((),v,false) from step]
    exact pairs _
  have a₀:coverNumber B ({a}:Support _)≤l:=by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using pairs anchor
  have meetings(v:V)(_v:v∈univ):¬Disjoint ({a}:Support _) (piece v):=by
    exact Finset.not_disjoint_iff.mpr ⟨a,Finset.mem_singleton_self _,Finset.mem_insert_self ..⟩
  have area:=cover_union_meeting B ({a}:Support _) piece univ meetings
  refine ⟨Z,Finset.mem_union_left _ (Finset.mem_singleton_self _),?_,?_⟩
  · intro v
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)
  · have summed:=Finset.sum_le_sum (fun v (_:v∈univ)=>costs v)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Z] using area.trans (add_le_add a₀ summed)

end YM.Integration.WilsonMeasuredPublicEntranceCommonHousing
end
