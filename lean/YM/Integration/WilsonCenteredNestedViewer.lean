import YM.Integration.WilsonCenteredNestedIntake
import YM.Integration.WilsonMacroscopicViewerCharge

/-! Insert the independently deposited complete graded packet in the true
ordinary exterior law. Each homogeneous component, including the unit, is
charged against its own original spectator reading on the fixed collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedViewer
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree
open Extraction Spec Table Filter WilsonCenteredNestedProgram WilsonCenteredNestedIntake
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n : ℕ} {p : Fin n → Tree} {I : Type} [Fintype I]

def predicted (A : Rule F Q) (g : ℝ→ℝ) (v : (fork n p).Leaf→S.Tag) (w : I→S.Tag)
    (H : ℕ) (D : (fork n p).Inner→ℕ) (s : (fork n p).Inner→ℝ) (z : (fork n p).Plot)
    (y : I→E4) (q : Viewers F) : ℂ :=
  ∑ j : Fin (H+1),∑ c : Q.channels j,
    run F Q A g (fork n p) s z v D j ⟨Fin.last j.val,c⟩ *
    (upon (spectator F q) j (anchor z) y (voices w)) (Q.actor j c)

theorem original (fac : Services C f S) (A : Rule F Q) (g L : ℝ→ℝ) (Ln : ∀ r,0 ≤ L r)
    (order : ℕ) (v : (fork n p).Leaf→S.Tag) (w : I→S.Tag)
    (H : ℕ) (D : (fork n p).Inner→ℕ) (M η ε δ : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η)
    (ep : 0 < ε) (dp : 0 < δ)
    (rows : localRows F Q A g L (fun a=>|g a|^order) M η (fork n p) v D H) :
    ∃ b : Fin (H+1)→ℝ,(∀j,0 ≤ b j) ∧
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner→ℝ) (z : (fork n p).Plot) (y : I→E4),
      Accept r M η s z → Buffer z y δ → ∀ q : Viewers F,
      ‖whole (spectator F q) (Tree.profile z) (voices v) y (voices w) -
        predicted F Q A g v w H D s z y q‖ ≤
      toll (wages v) ε (H+1:ℝ) s + ∑ j : Fin (H+1),∑ c : Q.channels j,
        (bothToll (wages v) ε j D s +
        WilsonCenteredNestedPhysical.vertexFee F Q s v D j L (fun a=>|g a|^order)) *
        (b j * ‖Q.actor j c‖) := by
  let paid := Nesting.uniform F Q fac
  have all (j : Fin (H+1)) : localRows F Q A g L (fun a=>|g a|^order) M η (fork n p) v D j :=
    ⟨fun sel k c=>rows.1 sel ⟨k.val,Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_succ (Nat.le_of_lt_succ j.isLt))⟩ c,rows.2⟩
  have panels := eventually_all.mpr (fun j : Fin (H+1)=>eventually_all.mpr (fun c : Q.channels j=>
    filed F Q paid A g L Ln order v D j c M η ε Mn ηp ep (all j)))
  choose b bn watch using fun j : Fin (H+1)=>WilsonMacroscopicViewerCharge.uniform F fac j (voices w) dp
  refine ⟨b,bn,?_⟩
  filter_upwards [paid.tested n p I v w H M η ε δ Mn ηp ep dp,panels] with r native compare
  intro s z y accept clear q
  have cert := native s z y accept clear
  have far : ClearOf (anchor z) y δ := ⟨fun i=>clear.1 (fork n p).topSeat i,clear.2⟩
  let heard (j : Fin (H+1)) (c : Q.channels j) :=
    (upon (spectator F q) j (anchor z) y (voices w)) (Q.actor j c)
  let exactRow (j : Fin (H+1)) (c : Q.channels j) := Kernel.output F Q z v c
  let other (j : Fin (H+1)) (c : Q.channels j) :=
    run F Q A g (fork n p) s z v D j ⟨Fin.last j.val,c⟩
  let price (j : Fin (H+1)) := bothToll (wages v) ε j D s +
    WilsonCenteredNestedPhysical.vertexFee F Q s v D j L (fun a=>|g a|^order)
  have node (j : Fin (H+1)) (c : Q.channels j) :
      ‖(exactRow j c-other j c)*heard j c‖ ≤ price j * (b j*‖Q.actor j c‖) := by
    have entry := compare j c s z accept
    rw [norm_mul]
    exact mul_le_mul entry (watch j (anchor z) y far cert.1.2.2 q (Q.actor j c))
      (norm_nonneg _) ((norm_nonneg _).trans entry)
  have total : ‖∑ j : Fin (H+1),∑ c : Q.channels j,(exactRow j c-other j c)*heard j c‖ ≤
      ∑ j : Fin (H+1),∑ c : Q.channels j,price j * (b j*‖Q.actor j c‖) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _=>(norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun c _=>node j c))))
  have eqn : whole (spectator F q) (Tree.profile z) (voices v) y (voices w) -
      predicted F Q A g v w H D s z y q =
      Kernel.pipe F Q z v q H y w + ∑ j : Fin (H+1),∑ c : Q.channels j,(exactRow j c-other j c)*heard j c := by
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    change _-(∑ j,∑ c,other j c*heard j c) =
      (_-(∑ j,∑ c,exactRow j c*heard j c))+((∑ j,∑ c,exactRow j c*heard j c)-(∑ j,∑ c,other j c*heard j c))
    abel
  rw [eqn]
  exact (norm_add_le _ _).trans (add_le_add (cert.2.2 q) total)

end YM.Integration.WilsonCenteredNestedViewer
