import YM.Integration.WilsonCenteredNestedRawRows

/-! One genuine binary fork inside a second binary fork, on the actual
inner center y(0) and its parent o.  The same rotation and real branch
are used at both ends of each fully deposited channel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRawPair
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open WilsonCenteredNestedRawRows WilsonCenteredNestedEdge
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
def placed {D : ℕ} (u : Menu.Cut Q D) (far : S.Tag) : Fin 2→S.Tag := ![oneTag F Q u.1 u.2,far]
lemma placed_grade {D : ℕ} (u : Menu.Cut Q D) (far : S.Tag) :
    degree (placed F Q u far) = u.1.val + far.1 := by simp [degree,placed,Fin.sum_univ_two,oneTag]

def held (D m : ℕ) (mc : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) (x y : Fin 2→E4) (o : E4) : ℂ :=
  ∑ t : Menu.Cut Q D, express Q t.1.val t.2 x v (y 0) * express Q m mc y (placed F Q t far) o

def joined (P : Prescription F.sector.derivatives) (D H m : ℕ) (mc : Q.channels m) (v : Fin 2→S.Tag)
    (far : S.Tag) (x y : Fin 2→E4) (o : E4) (k : Ortho) (b : Bool) : ℂ :=
  ∑ t : Menu.Cut Q D,face F Q P D t.1.val t.2 x v (y 0) k b *
      face F Q P H m mc y (placed F Q t far) o k b

theorem enlarge {n : ℕ} {P : Prescription F.sector.derivatives} {v : Fin n→S.Tag} {D : ℕ} {M η : ℝ}
    {j l : ℕ} {A B : ℝ} (jl : j ≤ l) (An : 0 ≤ A) (AB : A ≤ B) (old : Quoted F Q P v D M η j A) :
    Quoted F Q P v D M η l B := by
  filter_upwards [old,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r atR rp x o fit k b i c
  obtain ⟨difference,filed,raw⟩ := atR x o fit k b i c
  have change (m : ℕ) : wage j A r * WilsonCenteredNestedEdge.port r m (degree v) ≤ wage l B r * WilsonCenteredNestedEdge.port r m (degree v) :=
    mul_le_mul_of_nonneg_right (wage_le jl An AB) (by unfold WilsonCenteredNestedEdge.port;positivity)
  exact ⟨difference.trans (change _),filed.trans (change _),raw.trans (change _)⟩

/-- The projected-child error costs (a/r)^(D+1); the independently
assayed through-H root costs r^(H+1-m).  All intermediate grades are
retained in the complete original finite sum, including grade zero. -/
theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent) (fac : Facilities C f S)
    (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (D H m : ℕ) (mH : m ≤ H)
    (mc : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j l:ℕ)(A B:ℝ),0≤A ∧ 0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ),0<a → a≤r →
      ∀(x y:Fin 2→E4)(o:E4),WithinRoom a M η x (y 0) → WithinRoom r M η y o →
      ∀(k:Ortho)(b:Bool),‖held F Q D m mc v far x y o - joined F Q P D H m mc v far x y o k b‖ ≤
        Fintype.card (Menu.Cut Q D) * (wage j A a * wage l B r * base a r m (degree v) far.1 *
          ((a/r)^(D+1) + r^(H+1-m))) := by
  obtain ⟨j,A,An,inner⟩ := WilsonCenteredNestedRawRows.original F Q hp fac foundation lo ticket v D Mn ηp
  let prev := fun (t:Menu.Cut Q D) => Quoted F Q P (placed F Q t far) H M η
  obtain ⟨l,B,Bn,all⟩ := pool prev (fun _ _ _ _ _ jl An AB old=>enlarge F Q jl An AB old)
    (fun t=>WilsonCenteredNestedRawRows.original F Q hp fac foundation lo ticket (placed F Q t far) H Mn ηp)
  obtain ⟨ε,εp,below⟩ := (mem_nhdsGT_iff_exists_Ioc_subset.mp inner)
  refine ⟨j,l,A,B,An,Bn,?_⟩
  filter_upwards [eventually_all.mpr all,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds εp),
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r issued tight r1 a ap ar x y o close outer k b
  have near := below (show a ∈ Ioc 0 ε from ⟨ap,ar.trans tight⟩)
  unfold held joined
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le ..).trans ?_
  let bound := wage j A a * wage l B r * base a r m (degree v) far.1 * ((a/r)^(D+1)+r^(H+1-m))
  have total : ∑ _ : Menu.Cut Q D, bound = (Fintype.card (Menu.Cut Q D):ℝ) * bound := by simp [nsmul_eq_mul]
  rw [←total]
  apply Finset.sum_le_sum
  intro t _
  obtain ⟨nearDiff,_,nearRaw⟩ := near x (y 0) close k b t.1 t.2
  obtain ⟨farDiff,farPublic,_⟩ := issued t y o outer k b ⟨m,Nat.lt_succ_of_le mH⟩ mc
  rw [placed_grade] at farDiff farPublic
  have wn (l : ℕ) (B r : ℝ) (bn : 0 ≤ B) : 0 ≤ wage l B r :=
    mul_nonneg bn (pow_nonneg (zero_le_one.trans (shell_one r)) _)
  apply term ap ar r1 D H m (degree v) far.1 t.1.val (Nat.le_of_lt_succ t.1.isLt) mH _ _ _ _ (wn _ _ _ An) (wn _ _ _ Bn)
  · simpa only [norm_sub_rev] using nearDiff
  · simpa only [norm_sub_rev] using farDiff
  · exact nearRaw
  · exact farPublic

end YM.Integration.WilsonCenteredNestedRawPair
