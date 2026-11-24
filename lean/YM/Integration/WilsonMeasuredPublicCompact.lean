import YM.Integration.WilsonMeasuredPublicDocket

/-! A compact joint continuum profile with the stated physical separation fits the genuine original torus after both cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicCompact
open Function Filter Set Table Extraction Lattice Wilson Spec RG Climb Cells GapsContact GapsContact.Seams
open Trace.Terrace PhysicalNext.Repeat.Legato WilsonMeasuredPublicClearance WilsonMeasuredPublicLayout
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G) {N p:ℕ} {u v:Site (C.side N p)}

theorem component (u v:Site (C.side N p)) (i:Axis) :
    C.S.a N*((lift u i-lift v i).natAbs:ℝ) ≤ ‖C.S.place u-C.S.place v‖ := by
  have coord : |(C.S.place u-C.S.place v) i|=C.S.a N*((lift u i-lift v i).natAbs:ℝ) := by
    change |C.S.a N*(lift u i:ℝ)-C.S.a N*(lift v i:ℝ)|=_
    rw [← mul_sub,abs_mul,abs_of_pos (C.S.a_pos _),← Int.cast_sub,← Int.cast_abs,Int.abs_eq_natAbs]
    rfl
  rw [←coord]
  exact PiLp.norm_apply_le (C.S.place u-C.S.place v) i

/-- The large-period threshold depends only on the compact support, uniformly in N. -/
theorem distance {M:ℝ} (period:4*M < (C.S.period p).val)
    (hu:‖C.S.place u‖≤M) (hv:‖C.S.place v‖≤M) :
    ‖C.S.place u-C.S.place v‖ ≤ 2*(C.S.a N*(separation u v:ℝ)) := by
  let x:=lift u-lift v
  have central (i:Axis) : -((C.side N p).val:ℤ)<2*x i ∧ 2*x i≤(C.side N p).val := by
    have range : C.S.a N*((x i).natAbs:ℝ)≤2*M := (component C u v i).trans
      ((norm_sub_le _ _).trans (by linarith))
    have strict : C.S.a N*(2*((x i).natAbs:ℝ))<C.S.a N*((C.side N p).val:ℝ) := by
      rw [C.S.span_side]
      linarith
    have inside : 2*(x i).natAbs < (C.side N p).val := by
      exact_mod_cast lt_of_mul_lt_mul_left strict (C.S.a_pos N).le
    omega
  have rep : lift (u-v)=x := lift_eq_iff.mpr ⟨by simp [x],central⟩
  have same : C.S.place u-C.S.place v=C.S.place (u-v) := by
    change C.S.gridPoint N (lift u)-C.S.gridPoint N (lift v)=C.S.gridPoint N (lift (u-v))
    rw [rep]
    have add:=Work.B16.grid_add (C:=C) (k:=N) x (lift v)
    rw [show x+lift v=lift u from sub_add_cancel ..] at add
    exact (eq_sub_of_add_eq add.symm).symm
  rw [same]
  simpa only [separation,sub_zero,mul_assoc] using (MergeProof.Ribbons.normC C N p (u-v)).2

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {D T count n:ℕ} {δ r:ℝ}
    (board : WilsonMeasuredPublicClearance.Book F l (z:=z) D T count δ r)
local notation "mesh" => R.family.S.a

/-- One actual origin for each nonzero full profile, allowing a moving center in
a fixed compact region. Its pairwise diameter and separation are Euclidean.
All rooted geometry is then produced by the native positive Wilson law. -/
theorem placed (load:n≤count) {coarse packet:ℕ} (outerSeat:coarse≤packet)
    (room:10*mesh packet< mesh coarse) (floor:δ*r≤ mesh packet) (m:Fin n→ℕ)
    (walls:∀i,board.bank.m ≤ m i) (M:ℝ) (t:Test n)
    (supports:∀x:Points n,t x≠0→(∀i,‖x i‖≤M) ∧ (∀i j,‖x i-x j‖<3*mesh packet) ∧
       ∀i j,i≠j→2*(δ*r)≤‖x i-x j‖) :
    ∀ᶠ q:ℕ×ℕ in f.fuse,∀ u:Var R.family.S n q.1 q.2,t (Order.cells R.family q.1 q.2 u)≠0 →
      Nonempty (Placed R.family m u) := by
  have horizon : ∀ᶠ q:ℕ×ℕ in f.fuse,board.bank.m≤q.1 ∧ ∀i,m i ≤ q.1 :=
    (OPE.Cards.largeMesh f|>.eventually_ge_atTop _).and <|
       eventually_all.mpr fun i=>(OPE.Cards.largeMesh f).eventually_ge_atTop (m i)
  have large : ∀ᶠ q:ℕ×ℕ in f.fuse,4*M < (R.family.S.period q.2).val := by
    rw [Order.fused]
    have grows:Tendsto (fun p:ℕ=>((R.family.S.period p).val:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp R.family.S.period_strict.tendsto_atTop
    exact (f.per.cofinal.eventually (grows.eventually_gt_atTop (4*M))).mono fun p seen=>Eventually.of_forall fun _=>seen
  filter_upwards [horizon,large] with q active big
  intro u nonzero
  obtain ⟨bounded,diam,sep⟩:=supports (Order.cells R.family q.1 q.2 u) nonzero
  by_cases empty:Nonempty (Fin n)
  · let c:=empty.some
    apply WilsonMeasuredPublicDocket.located F board (by simpa using load) outerSeat room floor active.1 walls active.2
      (u c) u (fun i=>lift (u i)-lift (u c))
    · intro i; simp
    · intro i a
      exact (component R.family (u i) (u c) a).trans_lt (diam i c)
    · intro i j ne
      have lower:=sep i j ne
      have upper:=distance R.family big (bounded i) (bounded j)
      change 2*(δ*r)≤‖R.family.S.place (u i)-R.family.S.place (u j)‖ at lower
      linarith only [lower,upper]
  · letI : IsEmpty (Fin n):=not_nonempty_iff.mp empty
    apply WilsonMeasuredPublicDocket.located F board (by simp) outerSeat room floor active.1 walls active.2
      0 u (fun _=>0) (fun i=>isEmptyElim i) (fun i=>isEmptyElim i) (fun i=>isEmptyElim i)

end YM.Integration.WilsonMeasuredPublicCompact
