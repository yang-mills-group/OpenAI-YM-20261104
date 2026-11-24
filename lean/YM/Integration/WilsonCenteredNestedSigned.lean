import YM.Integration.WilsonCenteredNestedGross

/-! A signed comparable measurement suffices. The full physical gross is
already paid by the elected matrix. The independent gross follows by
adding the small signed discrepancy to this measured absolute price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedSigned
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open OPE.Nesting.Composite OPE.Log Filter Extraction Table Spec Trace.Pilot
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross WilsonCenteredNestedProgram WilsonCenteredNestedIntake
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def Signed (A : Rule F Q) (g : ℝ→ℝ) (M η : ℝ) (p k : ℕ) (B : ℝ) :
    (t : Tree) → (t.Leaf→S.Tag) → (t.Inner→ℕ) → ℕ → Prop
  | bud,_,_,_=>True
  | fork n arm,v,D,H=>
    (∀ (j : Branches F Q (f:=arm) (rollCaps D)) (m : Fin (H+1)) (c : Q.channels m),
      ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x : Fin n→E4) (o : E4),
        (∀ i,‖x i-o‖ ≤ M*r) → (∀ i l,i ≠ l → η*r ≤ ‖x i-x l‖) →
        let child := echoTags F Q v j
        ‖express Q m c x child o - A n m c r (g r) x child o‖ ≤
          wage k B r * (r^m.val / ∏ i,r^(child i).1) * |g r|^p) ∧
    ∀i,Signed A g M η p k B (arm i) (childWages i v) (childAge i D) (rollCaps D i)

theorem joined (simple : G.Simple) (g : ℝ→ℝ) (hg : Coupling G g)
    (A : Rule F Q) (p j k : ℕ) {B C : ℝ} (Bn : 0 ≤ B) (Cn : 0 ≤ C)
    {M η : ℝ} (t : Tree) (v : t.Leaf→S.Tag) (D : t.Inner→ℕ) (H : ℕ)
    (trueRows : localRows F Q (measured F Q) g (wage j B) (fun _=>0) M η t v D H)
    (independent : Signed F Q A g M η p k C t v D H) :
    localRows F Q A g (wage (j+k) (B+C)) (fun a=>|g a|^p) M η t v D H := by
  induction t generalizing H with
  | bud => trivial
  | fork n arm ih =>
    constructor
    · intro sel m c
      filter_upwards [trueRows.1 sel m c,independent.1 sel m c,hg.positive,
        (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),
        (show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r gross changed gp cap rp x o close cleared
      let child := echoTags F Q v sel
      let eng := r^m.val / ∏i,r^(child i).1
      let X := express Q m c x child o
      let Y := A n m c r (g r) x child o
      have en : 0 ≤ eng := div_nonneg (pow_nonneg rp.le _) (Finset.prod_nonneg (fun i _=>pow_nonneg rp.le _))
      have bn := (gross x o close cleared).left
      have miss := changed x o close cleared
      change ‖X‖ ≤ wage j B r * eng at bn
      change ‖X-Y‖ ≤ wage k C r * eng * |g r|^p at miss
      have low : |g r|^p ≤ 1 := by rw [abs_of_pos gp];exact pow_le_one₀ gp.le cap
      have p0 := mul_nonneg (mul_nonneg Cn (pow_nonneg (zero_le_one.trans (shell_one r)) k)) en
      have old : wage j B r ≤ wage (j+k) B r := wage_le (Nat.le_add_right ..) Bn le_rfl
      have newp : wage k C r ≤ wage (j+k) C r := wage_le (Nat.le_add_left ..) Cn le_rfl
      have together : wage (j+k) B r + wage (j+k) C r = wage (j+k) (B+C) r := by unfold wage;ring
      have rich : wage (j+k) B r ≤ wage (j+k) (B+C) r := wage_le le_rfl Bn (le_add_of_nonneg_right Cn)
      have fresh : wage (j+k) C r ≤ wage (j+k) (B+C) r := wage_le le_rfl Cn (le_add_of_nonneg_left Bn)
      refine ⟨bn.trans (mul_le_mul_of_nonneg_right (old.trans rich) en),?_,?_⟩
      · calc
          ‖Y‖ ≤ ‖X‖ + ‖X-Y‖ := norm_le_norm_add_norm_sub X Y
          _ ≤ wage j B r * eng + wage k C r * eng := add_le_add bn (miss.trans (mul_le_of_le_one_right p0 low))
          _ ≤ wage (j+k) B r * eng + wage (j+k) C r * eng :=
            add_le_add (mul_le_mul_of_nonneg_right old en) (mul_le_mul_of_nonneg_right newp en)
          _ = wage (j+k) (B+C) r * eng := by rw [←add_mul,together]
      · exact miss.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (newp.trans fresh) en)
          (pow_nonneg (abs_nonneg _) _))
    · exact fun i=>ih i _ _ _ (trueRows.2 i) (independent.2 i)

/-- The genuine measured exponent and scale constant precede the order,
independently assigned programme and its signed numerical fee. -/
theorem original (simple : G.Simple) (fac : Services C f S) (log : SingleLog F Q.port)
    (g : ℝ→ℝ) (hg : Coupling G g) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η)
    (t : Tree) (v : t.Leaf→S.Tag) (D : t.Inner→ℕ) (H : ℕ) :
    ∃ j B,0 ≤ B ∧ ∀ (k p : ℕ) (A : Rule F Q) (C : ℝ),0 ≤ C →
    Signed F Q A g M η p k C t v D H →
    localRows F Q A g (wage (j+k) (B+C)) (fun a=>|g a|^p) M η t v D H := by
  obtain ⟨j,B,bn,paid⟩ := WilsonCenteredNestedGross.original F Q fac log g Mn ηp t v D H
  exact ⟨j,B,bn,fun k p A C cn src=> joined F Q simple g hg A p j k bn cn t v D H paid src⟩

end YM.Integration.WilsonCenteredNestedSigned
