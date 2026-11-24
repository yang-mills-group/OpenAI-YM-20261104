import YM.Integration.WilsonAddressedPublicSelfCards
import YM.Integration.WilsonMeasuredPublicScatteredCells

/-! A common physical tiling for independently purchased reflected cutoff widths. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicSelfRoom
open Function Filter Set Table Extraction Lattice Wilson Spec RG Climb OPE Cards Cells Next.Phase Push
open GapsContact GapsContact.Seams Trace.Terrace PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicScatteredCells (Seats)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{I:Type}[Fintype I]{j m N p:ℕ}(k:I→ℕ)
    (u:I→Site (R.family.side N p))

theorem original (before:j ≤ m)(fresh:m ≤ N)(later:∀i,m ≤ k i)(live:∀i,k i ≤ N)
    (money:(Fintype.card I:ℝ)*(2*(3*R.family.S.a m))<R.family.S.a j)
    (apart:∀i i',i≠i' → R.family.S.a j<R.family.S.a N*(separation (u i) (u i'):ℝ)):
    Nonempty (Seats (R:=R) k u):=by
  have earlier:=before.trans fresh
  obtain ⟨x,_,room⟩:=OPE.Cards.seats R.family earlier le_rfl le_rfl before fresh
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
  refine ⟨⟨W,rfl,live,fun i=>Around.inherits (before.trans (later i)) (live i),fit,?_⟩⟩
  intro i t h
  by_contra ne
  change W.which (u i)=W.which (u t) at h
  have wide := W.extent (fit i).1 (show u t∈W.chamber (W.which (u i)) by rw [h];exact (fit t).1)
  have bad : R.family.S.a N*(separation (u i) (u t):ℝ)≤R.family.S.a j :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast wide : (separation (u i) (u t):ℝ)≤W.side.val)
      (R.family.S.a_pos _).le).trans_eq (R.family.S.embeds_scale _)
  exact (apart i t ne).not_ge bad

end YM.Integration.WilsonAddressedPublicSelfRoom
end
