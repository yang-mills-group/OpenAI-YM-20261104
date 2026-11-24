import YM.Integration.FVA1Physical.Marked.InvariantOperand
import YM.Work.F05.Actions

/-! Every calibrated physical basis field is a finite complex linear
combination of actual gauge-legal real native operands. The list is chosen
before the period and field. Gauge averaging is performed on separate
finite monomials, and invariance restores the exact physical sum. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Source Source.Drops Next.Foundations Stationary Marker Qlocal Qlocal.Quipu
open Qlocal.Quipu.Sonnet Qlocal.Quipu.Lasso Qlocal.Quipu.Zora MeasureTheory
open scoped Classical BigOperators
variable {G : Gauge} {k : ℕ}

private abbrev Word (G : Gauge) (k : ℕ) := ℂ × List (Fin k × G.ColorIndex)
private def Word.read (w : Word G k) (p : GaugePanel G k) : ℂ :=
  w.1 * (((w.2.map fun j => p j.1 j.2).prod : ℝ) : ℂ)

private theorem words (P : Bid.Pose G k) : ∃ L : List (Word G k),
    ∀ p : GaugePanel G k, Bid.lumin P p = (L.map fun w => w.read p).sum := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨[(a,[])],fun p=>by simp [Bid.lumin,Word.read]⟩
  | add a b h₁ h₂ =>
    obtain ⟨A,hA⟩ := h₁
    obtain ⟨B,hB⟩ := h₂
    refine ⟨A++B,fun p=>?_⟩
    simp only [List.map_append,List.sum_append,←hA,←hB,Bid.lumin,map_add]
  | mul_X a i h =>
    obtain ⟨A,hA⟩ := h
    refine ⟨A.map (fun w => (w.1,i::w.2)),fun p => ?_⟩
    rw [show Bid.lumin (a * MvPolynomial.X i) p = Bid.lumin a p * (p i.1 i.2 : ℂ) by simp [Bid.lumin],hA,←List.sum_map_mul_right]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro w _
    simp [Word.read,mul_left_comm,mul_comm]

private def Word.operand {I : Type} [DecidableEq I] {B : Census I} (w : Word G k)
    (s : Senses B) (S : Fin k→RG.Slot) : Vase s G w.2.length :=
  invariantOperand s (fun l => S (w.2.get l).1) (fun l => (w.2.get l).2)

private theorem Word.avg {I : Type} [DecidableEq I] {B : Census I} (w : Word G k)
    (s : Senses B) (S : Fin k→RG.Slot) {c : Side} (x : Site c) (q : ℕ) (v : Config G c) :
    w.1 * (((w.operand s S).read x q v : ℝ):ℂ) =
      ∫ u : G.El, w.read (fun j => G.adjoint u ((S j).atSite v x)) ∂G.probHaar := by
  rw [Word.operand, invariant_operand_eq]
  rw [show (fun u : G.El => w.read (fun j=> G.adjoint u ((S j).atSite v x))) =
    (fun u => w.1 * ((∏ i : Fin w.2.length,G.adjoint u ((S (w.2.get i).1).atSite v x) (w.2.get i).2 : ℝ):ℂ)) from ?_]
  · rw [integral_const_mul,integral_complex_ofReal]
  funext u
  unfold Word.read
  congr 2
  let f : Fin k × G.ColorIndex → ℝ := fun j => G.adjoint u ((S j.1).atSite v x) j.2
  change (w.2.map f).prod = ∏ i : Fin w.2.length, f (w.2.get i)
  calc
    (w.2.map f).prod = ((List.ofFn w.2.get).map f).prod := by rw [List.ofFn_get]
    _ = (List.ofFn (f ∘ w.2.get)).prod := congrArg List.prod (List.map_ofFn (g:=f) (f:=w.2.get))
    _ = _ := List.prod_ofFn

private theorem Word.nu (w : Word G k) (S : Fin k→RG.Slot) {c : Side} (x : Site c) (v : Config G c) :
    Integrable (fun u : G.El => w.read (fun j => G.adjoint u ((S j).atSite v x))) G.probHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  have cont (T : List (Fin k × G.ColorIndex)) : Continuous (fun u : G.El =>
      (T.map (fun j => G.adjoint u ((S j.1).atSite v x) j.2)).prod) := by
    induction T with
    | nil => simpa only [List.map_nil,List.prod_nil] using (continuous_const : Continuous fun _ : G.El => (1:ℝ))
    | cons j T ih => exact ((EuclideanSpace.proj _).continuous.comp (Zora.continuity _)).mul ih
  exact cont w.2

variable {I : Type} [DecidableEq I] {B : Census I}
/-- One pure native real program operand plus its outer physical complex
coefficient. The complete expansion employs only finitely many of these. -/
structure FieldOperand (s : Senses B) (G : Gauge) where
  order : ℕ
  code : Vase s G order
  factor : ℂ

theorem basis_album (s : Senses B) (d : ℕ) (i : ((Labels.frames G).level d).Index) :
    ∃ L : List (FieldOperand s G), ∀ (c : Side) (x : Site c) (q : ℕ) (v : Config G c),
      (localSection G d).places (Pi.single i 1) x v =
        (L.map (fun a=>a.factor*((a.code.read x q v:ℝ):ℂ))).sum := by
  let A := squareBasis G d i
  obtain ⟨W,hW⟩ := words A.polynomial
  let packet (w : Word G A.arity) : FieldOperand s G := ⟨w.2.length,w.operand s A.slot,w.1⟩
  refine ⟨W.map packet,?_⟩
  intro c x q v
  let F := (localSection G d).places (Pi.single i 1) x
  let test (u : G.El) := fun j => G.adjoint u ((A.slot j).atSite v x)
  have id (u : G.El) : (W.map (fun w => w.read (test u))).sum = F v := by
    rw [←hW]
    have h := (square_basis_spec d i).2.2 c x (gauge (fun _=>u) v)
    rw [(localSection G d).placed_invariant (sound G d) _ _ (fun _=>u) v] at h
    change Bid.lumin A.polynomial (fun j => G.adjoint u ((A.slot j).atSite v x)) = F v
    rw [←show (fun j => (A.slot j).atSite (gauge (fun _=>u) v) x) =
      fun j => G.adjoint u ((A.slot j).atSite v x) from funext fun j=> Work.F05.slot_gauge ..]
    let z := gauge (fun _=>u) v
    have he : Bid.lumin A.polynomial (fun j => (A.slot j).atSite z x) = A.read x z :=
      congrArg (Bid.lumin A.polynomial) (funext fun j => Work.F02.atSite_curvature (A.slot j) z x)
    exact he.trans h.symm
  have add (W' : List (Word G A.arity)) :
      Integrable (fun u:G.El=> (W'.map fun w => w.read (test u)).sum) G.probHaar ∧
      (∫ u:G.El, (W'.map fun w => w.read (test u)).sum ∂G.probHaar) =
        (W'.map (fun w=>w.1*(((w.operand s A.slot).read x q v:ℝ):ℂ))).sum := by
    induction W' with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons,List.sum_cons]
      refine ⟨(w.nu A.slot x v).add ih.1,?_⟩
      rw [integral_add (w.nu A.slot x v) ih.1,←w.avg s A.slot x q v,ih.2]
  calc
    F v = ∫ u:G.El, (W.map fun w=>w.read (test u)).sum ∂G.probHaar := by simp only [id,integral_const,probReal_univ,one_smul]
    _ = _ := (add W).2.trans (by simp [packet,List.map_map,Function.comp_def])

end YM.Integration.FVA1Physical.Marked
