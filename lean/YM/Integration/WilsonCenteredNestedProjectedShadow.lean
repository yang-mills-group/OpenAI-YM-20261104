import YM.Integration.WilsonCenteredNestedRealOrbit

/-! Literal signed coordinates of the complete through-degree raw field in
the public reader, with all lower fields reconstructed on that same reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedProjectedShadow
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

def read (m h : ℕ) (c : Q.channels m) : S.Field h →ₗ[ℂ] ℂ :=
  ((Q.basis m).coord c).comp ((Q.stratum m).subtype.leftInverse.comp (Q.cutTest m h))

lemma on_packet (m h : ℕ) (mh : m ≤ h) (c : Q.channels m) (x : I→E4) (v : Labels S d) (o : E4) :
    read F Q m h c (Q.packet h x v o) = Q.coef m c x v o := by
  let z : Q.stratum m := ⟨Q.fresh m x o v,Q.fresh_mem m x o v⟩
  unfold read
  rw [LinearMap.comp_apply,LinearMap.comp_apply,Q.filtered_packet m h mh]
  change (Q.basis m).coord c ((Q.stratum m).subtype.leftInverse z.val) = (Q.basis m).coord c z
  have back : (Q.stratum m).subtype.leftInverse z.val = z := LinearMap.leftInverse_apply_of_inj (Q.stratum m).ker_subtype z
  rw [back]

/-- Reassembling all retained numeric readings reproduces the original
field, including a nonzero unit coordinate. -/
lemma assemble (h : ℕ) (v : S.Field h) :
    ∑ j : Fin (h+1),∑ c : Q.channels j.val,
      read F Q j.val h c v • F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (Q.actor j.val c) = v := by
  let w : Labels S (fun _:Unit=>h) := sole v
  have unity : Q.packet h (sole 0) w 0 = v := by
    rw [Q.packet_single h h le_rfl v]
    exact F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts v
  rw [←unity]
  conv_rhs => unfold Reader.packet
  refine Finset.sum_congr rfl fun j _=>?_
  simp_rw [on_packet F Q _ _ (Nat.le_of_lt_succ j.isLt)]
  rw [←Q.assemble j.val (sole 0) w 0,map_sum]
  exact Finset.sum_congr rfl fun c _=>(F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)).map_smul _ _ |>.symm

/-- One uniform bank of absolute grade-D+1 fees for all projected
lower readings of each of the two original real branches at every rotation. -/
theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j : ℕ)(A : ℝ),0 ≤ A ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:I→E4)(o:E4),WithinRoom r M η x o →
      ∀(k:Ortho)(b:Bool)(i:Fin (h+1))(c:Q.channels i.val),
      ‖read F Q i.val h c (WilsonCenteredNestedRealOrbit.restored F P h x v o k b) - Q.coef i.val c x v o‖ ≤
        wage j A r * r^((h:ℝ)+1-weight d) := by
  let T := Σ i : Fin (h+1),Q.channels i.val
  let L (t : T) := (read F Q t.1.val h t.2).toContinuousLinearMap
  let total := ∑ t : T,‖L t‖
  have bound (t : T) : ‖L t‖ ≤ total := Finset.single_le_sum (fun i _=>(L i).opNorm_nonneg) (Finset.mem_univ t)
  have nn : 0 ≤ total := Finset.sum_nonneg fun t _=>(L t).opNorm_nonneg
  obtain ⟨j,A,An,earned⟩ := WilsonCenteredNestedRealOrbit.original F Q hp fac foundation lo ticket h v Mn ηp
  refine ⟨j,total*A,mul_nonneg nn An,?_⟩
  filter_upwards [earned] with r actual x o fit k b i c
  rw [←on_packet F Q i.val h (Nat.le_of_lt_succ i.isLt) c x v o,←map_sub]
  calc
    _ ≤ ‖L ⟨i,c⟩‖ * _ := (L ⟨i,c⟩).le_opNorm _
    _ ≤ total * _ := mul_le_mul (bound ⟨i,c⟩) (actual x o fit k b) (norm_nonneg _) nn
    _ = _ := by unfold wage;ring

end YM.Integration.WilsonCenteredNestedProjectedShadow
