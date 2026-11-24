import YM.Integration.WilsonMeasuredPublicCompact

/-! Distinct physical cells suffice for the ordinary full moment at arbitrary ambient diameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicScatteredCells
open Function Filter Set Table Extraction Lattice Wilson Spec RG Climb OPE Cards Cells Next.Phase Push
open GapsContact GapsContact.Seams Trace.Terrace PhysicalNext.Repeat.Legato WilsonMeasuredPublicClearance
open scoped Classical Topology BigOperators
variable {I:Type} [Fintype I] {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {l:Ultrafilter (ℕ×ℕ)} {z:Arch R.family}
    {D T count:ℕ} {δ r:ℝ} (board:WilsonMeasuredPublicClearance.Book F l (z:=z) D T count δ r)
    {N p:ℕ} {m:I→ℕ} (u : I→Site (R.family.side N p))
local notation "C!" => R.family

/-- Each original source has its own full-reflection root on the common tiling.
The cells can be arbitrarily far apart in physical space. -/
structure Seats (m:I→ℕ) (u:I→Site (R.family.side N p)) where
  tile : Tiling (R.family.side N p)
  upright : tile.kind=.link
  live : ∀i,m i≤N
  divides : ∀i,Cells.span R.family.S (live i) p ∣ tile.side.val
  sits : ∀i,Inside tile (3*Cells.span R.family.S (live i) p) (u i)
  distinct : Injective (fun i=>tile.which (u i))

theorem arranged (size:Fintype.card I ≤ count) (fresh:board.bank.m≤N) (later:∀i,board.bank.m ≤ m i)
    (live:∀i,m i≤N) (apart:∀i j,i≠j→δ*r≤R.family.S.a N*(separation (u i) (u j):ℝ)) :
    Nonempty (Seats (R:=R) m u) := by
  have earlier:=board.before.trans fresh
  have card:(Fintype.card I:ℝ)≤count:=by exact_mod_cast size
  have money : (Fintype.card I:ℝ)*(2*(3*R.family.S.a board.bank.m))<R.family.S.a board.micro := by
    have h:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left card (by norm_num : (0:ℝ)≤6))
      (R.family.S.a_pos board.bank.m).le).trans_lt board.slack
    linarith
  obtain ⟨x,_,room⟩:=OPE.Cards.seats R.family earlier le_rfl le_rfl board.before fresh
    (fun _ : Empty=>0) u (by simp [R.family.S.a_pos]) money
  let W:=(center R.family.S p earlier (0:Site (R.family.side N p))).newly x
  have sub (i:I) : Cells.span R.family.S (live i) p ∣ Cells.span R.family.S fresh p := Around.inherits (later i) (live i)
  have fit (i:I) : Inside W (3*Cells.span R.family.S (live i) p) (u i) := by
    have hi:=(inside_stripe W rfl _ _).mp (room i)
    have le:= Nat.le_of_dvd (R.family.S.toDepth fresh p).count.property (sub i)
    apply (inside_stripe W rfl _ _).mpr
    intro a
    obtain ⟨v,w⟩:=hi a
    exact ⟨(Nat.mul_le_mul_left 3 le).trans v,(Nat.add_le_add_left (Nat.mul_le_mul_left 3 le) _).trans_lt w⟩
  refine ⟨⟨W,rfl,live,fun i=>Around.inherits (board.before.trans (later i)) (live i),fit,?_⟩⟩
  intro i j h
  by_contra ne
  change W.which (u i)=W.which (u j) at h
  have wide := W.extent (fit i).1 (show u j∈W.chamber (W.which (u i)) by rw [h];exact (fit j).1)
  have bad : R.family.S.a N*(separation (u i) (u j):ℝ)≤R.family.S.a board.micro :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast wide : (separation (u i) (u j):ℝ)≤W.side.val)
      (R.family.S.a_pos _).le).trans_eq (R.family.S.embeds_scale _)
  exact (bad.trans_lt board.small).not_ge (apart i j ne)

theorem heard (board:Seats (R:=R) m u) {C:I→ Config G (R.family.side N p)→ℂ} {K:I→ℝ}
    (past:∀i,Cards.PaidAt R.family.S N p (m i) (R.family.beta N p) (K i) (C i))
    (seam:Seam G (R.family.side N p) (R.family.beta N p)) :
    ∃P:I→ Config G (R.family.side N p)→ℂ,
      (∀i,board.tile.copy (board.tile.which (u i)) (P i)=(fun U=>C i (translate (u i) U)) ∧
        Interior (board.tile.chamber 0) (P i) ∧ board.tile.rootTest (R.family.beta N p) (P i)≤K i) ∧
      ‖moment (R.family.beta N p) (fun U=>∏i,C i (translate (u i) U))‖≤∏i,K i := by
  let W:=board.tile
  have filed (i:I) : ∃ Y:Config G (R.family.side N p)→ℂ,
      W.copy (W.which (u i)) Y=(fun U=>C i (translate (u i) U)) ∧ Interior (W.chamber 0) Y ∧
      W.rootTest (R.family.beta N p) Y≤K i := by
    obtain ⟨x,b,s,_,_,_,same,owned,priced⟩ := (past i).at_cell W false 1 rfl (board.divides i) (board.sits i) seam
    refine ⟨_,?_,owned,priced⟩
    funext U
    rw [same,RelayDifference.oriented,pull_one]
    rfl
  choose P emitted enabled wage using filed
  refine ⟨P,fun i=>⟨emitted i,enabled i,wage i⟩,?_⟩
  have joints : (fun U=>∏i,C i (translate (u i) U))=(fun U=>∏i,W.copy (W.which (u i)) (P i) U) := by
    funext U
    exact Finset.prod_congr rfl fun i _=>(congr_fun (emitted i) U).symm
  rw [joints]
  exact (W.planted seam _ board.distinct P enabled).trans
    (Finset.prod_le_prod (fun i _=>W.root_nonneg ..) (fun i _=>wage i))

end YM.Integration.WilsonMeasuredPublicScatteredCells
