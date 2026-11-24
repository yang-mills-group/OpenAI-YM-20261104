import YM.Integration.WilsonIndependentFittedExteriorPlateBudget

/-! The actual adjacent two-moment rung containing the requested exterior
radius. The power bound comes from the purchased patches on that plate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorRuler
open Lattice RG XSpace RegulatorIR RegulatorIR.Ledger
open WilsonCoeffUV
open WilsonIndependentExactPlate (Requests)
open scoped Classical

theorem adjacent (S:Schedule)(s m:ℕ)(ordered:s ≤ m)(reach:ℝ)(near:1 ≤ reach)(room:reach ≤ S.a s/S.a m):
    ∃t,s ≤ t ∧ t ≤ m ∧ 1 ≤ reach/(S.a t/S.a m) ∧
      ((t=s ∧ reach/(S.a t/S.a m)=1) ∨
        (s<t ∧ reach/(S.a t/S.a m)<((S.block (t-1)).val:ℝ))):=by
  have ok:∃t:ℕ,s ≤ t ∧ t ≤ m ∧ S.a t/S.a m ≤ reach:=⟨m,ordered,le_rfl,by simpa [(S.a_pos m).ne']⟩
  let t:=Nat.find ok
  obtain ⟨lo,hi,hit⟩:=Nat.find_spec ok
  have pay:S.a t/S.a m ≤ reach:=hit
  have warm:0<S.a t/S.a m:=div_pos (S.a_pos _) (S.a_pos _)
  refine ⟨t,lo,hi,(one_le_div warm).2 pay,?_⟩
  by_cases bound:t=s
  · left
    refine ⟨bound,?_⟩
    rw [show reach=S.a t/S.a m from le_antisymm (bound ▸ room) pay,div_self warm.ne']
  · right
    have lo':s<t:=lt_of_le_of_ne lo (Ne.symm bound)
    have back:t-1<t:=by omega
    have older:reach<S.a (t-1)/S.a m:=by
      apply lt_of_not_ge
      intro past
      exact Nat.find_min ok back ⟨by omega,by omega,past⟩
    have step:(t-1)+1=t:=by omega
    have split:=S.a_step (t-1)
    rw [step] at split
    have size:0<(S.block (t-1)).val:= (S.block _).pos
    refine ⟨lo',(div_lt_iff₀ warm).2 ?_⟩
    calc reach<S.a (t-1)/S.a m:=older
         _=(S.block (t-1)).val*(S.a t/S.a m):=by rw [split];field_simp

theorem original {G:Gauge}(V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4 ≤ j)(i:Requests a)(A:Levels G)(s m:ℕ)
    (placed:s ≤ m)(close:m ≤ s+WilsonIndependentExactPlate.M V a i)
    (acts:∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i→
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha j hj).pactP f)
    (reach:ℝ)(near:1 ≤ reach)(room:reach ≤ A.S.a s/A.S.a m):
    ∃t,s ≤ t ∧ t ≤ m ∧ 1 ≤ reach/(A.S.a t/A.S.a m) ∧
      reach/(A.S.a t/A.S.a m) ≤ (V.ratio:ℝ)^(2*a):=by
  obtain ⟨t,lo,hi,bought,exact₀|old⟩:=adjacent A.S s m placed reach near room
  · refine ⟨t,lo,hi,bought,?_⟩
    rw [exact₀.2]
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ V.ratio by have h:=V.large;omega))
  · let n:=WilsonIndependentExactPlate.M V a i
    have back: s ≤ t-1:=by omega
    have avail:t-1<s+n:=by dsimp only [n];omega
    let f:Flap (WilsonIndependentExactPlate.M V a):=⟨i,s+n-t,by dsimp only [n] at *;omega⟩
    have address:s+(n-(f.offset+1))=t-1:=by dsimp only [f];omega
    have material:=congrArg Patch.L (acts f rfl)
    change A.S.block (s+(n-(f.offset+1)))=WilsonIndependentExactPlate.sizeL V a f at material
    rw [address] at material
    have cost:(A.S.block (t-1)).val ≤ V.ratio^(2*a):=by
      rw [material]
      change V.ratio^(if f.offset=0 then a+WilsonIndependentExactPlate.residue a f.volW else a) ≤ _
      apply Nat.pow_le_pow_right (by have:=V.large;omega)
      have rem:=Nat.mod_lt f.volW.val ha
      unfold WilsonIndependentExactPlate.residue
      split <;> omega
    exact ⟨t,lo,hi,bought,old.2.le.trans (by exact_mod_cast cost)⟩

end YM.Integration.WilsonIndependentFittedExteriorRuler
