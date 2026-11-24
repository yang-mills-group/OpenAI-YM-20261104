import YM.SchemeConversionRG11.Coupling.Profile
import YM.SchemeConversionRG11.Read.Supply

/-! The disconnected terms for the coupling triad at leading order. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Coupling

open Function Filter Maxwell Maxwell.Wick Issue Tape Pert.Position Pert.Triangle Extra.FD
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G}

private lemma odd_alone (x : Points 1) :
    moment G x (fun _ ↦ writes F 6 (basic F 0)) = 0 := by
  let p : Fin 1 → WickPol G := fun _ ↦ writes F 6 (basic F 0)
  have hf : (reversePol G ∘ p) = fun i ↦ (-1:ℂ) • p i := funext (fun i ↦
    (odd_reversed F).trans (neg_one_smul ℂ _).symm)
  have H := Wick_flip G x p
  rw [hf, MultilinearMap.map_smul_univ, Fin.prod_univ_one, neg_one_smul] at H
  exact neg_eq_self.mp H

private lemma odd_bu (h : G.Simple) (x : Points 2) {j : Fin 3} (hj : j ≠ 0) :
    moment G x ![writes F 6 (basic F 0), writes F 6 (basic F j)] = 0 := by
  let p := ![writes F 6 (basic F 0), writes F 6 (basic F j)]
  let k := ![(-1:ℂ),1]
  have hf : (reversePol G ∘ p) = fun i ↦ k i • p i := by
    funext i; fin_cases i
    · exact (odd_reversed F).trans (neg_one_smul ℂ _).symm
    exact (low_reversal h F (lower_basic F j hj)).trans (one_smul ℂ _).symm
  have H := Wick_flip G x p
  rw [hf, MultilinearMap.map_smul_univ, Fin.prod_univ_two, show k 1 = 1 from rfl, mul_one,
    show k 0 = -1 from rfl, neg_one_smul] at H
  exact neg_eq_self.mp H

private lemma one_alone (x : Points 1) (hx : x ∈ conf 1) {j : Fin 3} (hj : j ≠ 0) :
    moment G x (fun _ ↦ writes F 6 (basic F j)) = 0 := by
  classical
  rw [write_minus F j hj, Next.Rank.Normal.Wick_reads hx]
  have hz : Next.Rank.Normal.frameX (G:=G) hx = 0 := by
    apply Next.Rank.Normal.Symmetric.ext
    funext a b; change ite _ _ _ = 0; rw [if_pos (Subsingleton.elim a.1 b.1)]
  rw [Fin.prod_univ_one, hz, Next.Rank.Normal.blend_components, Next.Rank.Normal.froze]
  have he : reduceEq (uMinus G) =
    (2:ℂ)⁻¹ • (∑ i : Fin 3, ∑ t : G.ColorIndex, Maxwell.symbol 0 (Pert.Triangle.probe false i t) ^ 2) := freeMinus
  rw [he,map_smul,map_smul]
  simp [Maxwell.symbol]

private lemma two_even (x : Points 2) (hx : x ∈ conf 2) :
    moment G x ![writes F 6 (basic F 1), writes F 6 (basic F 2)] = 0 := by
  classical
  rw [write_minus F _ (by decide), write_minus F _ (by decide)]
  obtain ⟨y,hy⟩ := Set.Finite.exists_notMem (Set.finite_range (WithLp.ofLp x))
  let z := Points.cons y x
  have hz : z ∈ conf 3 := Work.A01.conf_cons hx (fun i h ↦ hy ⟨i,h.symm⟩)
  have he := writes_through F 6 ((freeTable F).unit 6)
  rw [writes_unit F 6] at he
  let a := reduceEq (uMinus G)
  change moment G x ![a,a] = 0
  have H : Fin.cons (α:=fun _ : Fin 3 ↦ WickPol G) 1 ![a,a] = UVNext.FreeStress.triangle 1 a a := by
    funext i; fin_cases i <;> rfl
  rw [Wick.adjoin hx y, H]; exact shift_at_outer (x:=z) hz he

private theorem kill_read {m : ℕ} (v : Fin m → E F 6) (t : Test m)
    (h : ∀ x ∈ conf m, moment G x (fun i ↦ writes F 6 (v i)) = 0) :
    gaussian F 6 t v = 0 := by
  rw [gauss_at]
  change t.applyTo _ = _
  apply Eq.trans (Test.apply_eq t (P:=fun _ ↦ 0) _) (by simp [Test.applyTo])
  intro x hx; exact (writes_eval F x (fun i ↦ ⟨6,v i⟩)).trans (h x hx)

theorem kill_single (i : Fin 3) (t : Test 1) : gaussian F 6 t (fun _ ↦ basic F i) = 0 := by
  by_cases hi : i = 0
  · subst i; exact kill_read _ _ (fun x _ ↦ odd_alone x)
  exact kill_read _ _ (fun x hx ↦ one_alone x hx hi)

theorem kill_odd_pair (h : G.Simple) (t : Test 2) {j : Fin 3} (hj : j ≠ 0) :
    gaussian F 6 t ![basic F 0,basic F j] = 0 := by
  apply kill_read; intro x _
  convert! odd_bu (F:=F) h x hj using 2
  funext k; fin_cases k <;> rfl

theorem kill_even_pair (t : Test 2) :
    gaussian F 6 t ![basic F 1,basic F 2] = 0 := by
  apply kill_read; intro x hx
  convert! two_even (F:=F) x hx using 2
  funext k; fin_cases k <;> rfl

end YM.SchemeConversionRG11.Coupling
