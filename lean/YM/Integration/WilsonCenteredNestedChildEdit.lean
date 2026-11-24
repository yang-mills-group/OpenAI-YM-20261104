import YM.Integration.WilsonCenteredNestedRawPair

/-! Change the entire nonroot child first, keeping its original terminal
row, orientation and real branch.  There is then only the child-ratio
error, uniformly in the actual child and parent radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedChildEdit
open Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom
open OPE.Log OPE.Prescription WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair WilsonCenteredNestedEdge
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def exitRow (D m : ℕ) (mc : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) (x y : Fin 2→E4) (o : E4)
    (k : Ortho) (b : Bool) : ℂ :=
  ∑ t : Menu.Cut Q D, express Q t.1.val t.2 x v (y 0) * face F Q Q.port m m mc y (placed F Q t far) o k b

theorem original (fac : Facilities C f S) (foundation : Foundation F Q)
    {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (D m : ℕ)
    (mc : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j l:ℕ)(A B:ℝ),0≤A ∧ 0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ),0<a → a≤r →
      ∀(x y:Fin 2→E4)(o:E4),WithinRoom a M η x (y 0) → WithinRoom r M η y o →
      ∀(k:Ortho)(b:Bool),‖joined F Q Q.port D m m mc v far x y o k b - exitRow F Q D m mc v far x y o k b‖ ≤
        Fintype.card (Menu.Cut Q D) * (wage j A a * wage l B r * base a r m (degree v) far.1 * (a/r)^(D+1)) := by
  obtain ⟨j,A,An,small⟩ := WilsonCenteredNestedRawRows.original F Q Q.spans fac foundation lo ticket v D Mn ηp
  let prev := fun (t:Menu.Cut Q D) => Quoted F Q Q.port (placed F Q t far) m M η
  obtain ⟨l,B,Bn,all⟩ := pool prev (fun _ _ _ _ _ jl An AB old=>enlarge F Q jl An AB old)
    (fun t=>WilsonCenteredNestedRawRows.original F Q Q.spans fac foundation lo ticket (placed F Q t far) m Mn ηp)
  obtain ⟨ε,εp,below⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp small
  refine ⟨j,l,A,B,An,Bn,?_⟩
  filter_upwards [eventually_all.mpr all,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds εp),
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r issued tight r1 a ap ar x y o close outer k b
  have near := below (show a ∈ Ioc 0 ε from ⟨ap,ar.trans tight⟩)
  unfold exitRow joined
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le ..).trans ?_
  let W := wage j A a * wage l B r
  let E := base a r m (degree v) far.1 * (a/r)^(D+1)
  have total : ∑ _ : Menu.Cut Q D, W*E = (Fintype.card (Menu.Cut Q D):ℝ)*(W*E) := by simp [nsmul_eq_mul]
  rw [mul_assoc (wage j A a * wage l B r),←total]
  apply Finset.sum_le_sum
  intro t _
  have change := (near x (y 0) close k b t.1 t.2).1
  have stay := (issued t y o outer k b (Fin.last m) mc).2.2
  change ‖face F Q Q.port m m mc y (placed F Q t far) o k b‖ ≤ wage l B r * WilsonCenteredNestedEdge.port r m (degree (placed F Q t far)) at stay
  rw [placed_grade] at stay
  rw [←sub_mul,norm_mul]
  refine (mul_le_mul change stay (norm_nonneg _) ((norm_nonneg _).trans change)).trans ?_
  have rp := ap.trans_le ar
  have E0 : 0 ≤ E := by dsimp [E,base];positivity
  have W0 : 0 ≤ W := by
    dsimp [W,wage]
    exact mul_nonneg (mul_nonneg An (pow_nonneg (zero_le_one.trans (shell_one a)) _)) (mul_nonneg Bn (pow_nonneg (zero_le_one.trans (shell_one r)) _))
  calc
    _ = W * (WilsonCenteredNestedEdge.port a (D+1) (degree v) * WilsonCenteredNestedEdge.port r m (t.1.val+far.1)) := by dsimp [W];ring
    _ = W * (E * r^(D+1-t.1.val)) := by rw [WilsonCenteredNestedEdge.inner ap rp D m _ far.1 _ (Nat.le_of_lt_succ t.1.isLt)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right E0 (pow_le_one₀ rp.le r1)) W0

end YM.Integration.WilsonCenteredNestedChildEdit
