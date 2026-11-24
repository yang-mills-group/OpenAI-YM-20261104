import YM.Dict06.Wilson.Slot
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Empirical

/-! An arbitrary section on the actual cover stencil in exponential link
coordinates, with full coefficient prescription including transport implied
by any of its admissible path expressions. The definition itself is from the
positive-link variables and their conjugates of evalC, no choice of a path
presentation and no lookup in an interacting label table. All terms are
at one root (translate on placement). Unmasked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Wil
open PowerSeries Function Series Lattice Wilson Bid Labels Source
open scoped BigOperators Matrix.Norms.Frobenius Topology ContDiff Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {Y : Finset Cover} {d : ℕ} {F : Frame G d}

abbrev Panel (Y : Finset Cover) (G : Gauge) := UsedEdges Y → G.Color

def restrictLog (Y : Finset Cover) (A : Links ℤ G.Color) : Panel Y G :=
  fun l => A l.val

def flag (i : Fin G.repDim) (j : Fin G.repDim) (b : Bool) : G.Mat →L[ℝ] ℂ :=
  let L := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
  if b then (starL' ℝ : ℂ≃L[ℝ]ℂ).toContinuousLinearMap ∘L L else L

lemma flag_eval (i : Fin G.repDim) (j : Fin G.repDim) (b : Bool) (m : G.Mat) :
    flag i j b m = if b then star (m i j) else m i j := by cases b <;> rfl

def lit (A : Panel Y G) (i : Source.Index G Y) :=
  flag i.2.1 i.2.2.1 i.2.2.2 (G.mat (G.lieExp (A i.1)))

def echo (S : SectionData F) (p : F.Coeff) (A : Panel S.stencil G) : ℂ :=
  MvPolynomial.eval (lit A) (S.evalC p)

lemma echo_exact (S : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) (t : ℝ) :
    S.evaluate p (positive A t) = echo S p (t • restrictLog S.stencil A) := by
  have he : Source.entry (S:=S.stencil) (positive A t) = lit (t • restrictLog S.stencil A) := by
    funext i; unfold Source.entry lit; rw [flag_eval]; rfl
  unfold SectionData.evaluate echo; rw [he]; rfl -- aeval-eval defeq?

lemma lit_smooth (i:Source.Index G Y) : ContDiff ℝ ω (fun A : Panel Y G=>lit A i) := by
  unfold lit; exact (flag _ _ _).contDiff.comp ((G.exp_jet).comp (contDiff_apply ℝ G.Color _))
lemma echo_smooth (S : SectionData F) (p : F.Coeff) : ContDiff ℝ ω (echo S p) := by
  unfold echo
  generalize S.evalC p=x
  induction x using MvPolynomial.induction_on with
  | C x=> simp; exact contDiff_const
  | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
  | mul_X p i hp=> simp_rw [map_mul,MvPolynomial.eval_X]; exact hp.mul (lit_smooth ..)

def ink (A : Panel Y G) (i:Source.Index G Y) : PowerSeries ℂ :=
  PowerSeries.mk fun n => flag i.2.1 i.2.2.1 i.2.2.2
                  ((n.factorial:ℝ)⁻¹ • (G.colorMat (A i.1))^n)

def book (S : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) :=
  poly (ink (restrictLog S.stencil A)) (S.evalC p)

lemma honest_ink (A : Panel Y G) (i:Source.Index G Y) :
    ps (fun t:ℝ=> lit (t • A) i)= ink A i := by
  let L := flag (G:=G) i.2.1 i.2.2.1 i.2.2.2
  let B := G.colorMat (A i.1)
  let f := fun t:ℝ=>NormedSpace.exp (t • B)
  have h : ContDiff ℝ ω f := G.contDiff_exp.comp (f:=fun t:ℝ=>t•B) (contDiff_id.smul contDiff_const)
  rw [show (fun t:ℝ=>lit (t • A) i)= L ∘ f from funext (fun t=>by simp [lit,f,L,B])]
  ext1 n
  rw [ps_at]; erw [ordinary_map _ n (h.contDiffAt.of_le le_top) L]; unfold ordinary f; erw [iterated_exp_mul]; simp [ink,L,B]; exact Or.inl rfl

lemma echo_book (S : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) :
    ps (fun t:ℝ=> S.evaluate p (positive A t))=book S p A := by
  let q:=restrictLog S.stencil A
  let a (i:Source.Index G S.stencil) (t:ℝ):=lit (t • q) i
  have he := readPoly_ps a (S.evalC p) (fun i=>(((lit_smooth i).of_le le_top).comp (g:=fun v=>lit v i) (f:=fun t:ℝ=>t • q) (contDiff_id.smul contDiff_const)).contDiffAt)
  simp_rw [echo_exact]; change ps (readPoly a (S.evalC p)) = _
  unfold book; exact he.2.trans (congrArg (fun a=>poly a (S.evalC p)) (funext (honest_ink q)))

/-- Rank-n presentation (symmetrized at the root, finite support on its
ordered positive-edge letters, all endpoint reservations in S.stencil). -/
def author (S : SectionData F) (p : F.Coeff) (n : ℕ) := Tensor.coeff (echo S p) n 0
lemma reported (S : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) (n : ℕ) :
    coeff n (book S p A) = Tensor.diagonal (author S p n) (restrictLog S.stencil A) := by
  rw [← echo_book,ps_at]; simp_rw [echo_exact]
  apply radial_eq; exact (echo_smooth S p).contDiffAt.of_le le_top

lemma locality (S : SectionData F) (p : F.Coeff) : LocalOn S.stencil (book S p) := by
  intro U V h
  have he : restrictLog S.stencil U=restrictLog S.stencil V:=funext fun x=>h x.val x.property.1 x.property.2
  unfold book; rw [he]

lemma graded (S : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) (n : ℕ) (t : ℝ) :
    coeff n (book S p (t • A)) = t^n • coeff n (book S p A) := by
  rw [reported,reported,show restrictLog S.stencil (t • A)= t • restrictLog S.stencil A from rfl, Tensor.homogeneous]

lemma via_paths (S : SectionData F) (i : F.Index) {m:ℕ} (B: Fin m→ RG.Slot) (P:Pose G m)
    (he : S.evaluate (Pi.single i 1) = lumin P ∘ mapped B) (A : Links ℤ G.Color) :
    book S (Pi.single i 1) A = poseSymbol A B P := by
  rw [← echo_book,he]; exact (honest_pose A B P).2

lemma book_start (S : SectionData F) (hp : Bid.pop S) (i:F.Index) :
    ∃ (m:ℕ) (B:Fin m→RG.Slot) (P:Pose G m),
      (∀ b,(B b).stencil ⊆ S.stencil) ∧
      ∀ A : Links ℤ G.Color,
        book S (Pi.single i 1) A = poseSymbol A B P ∧
        Initial (F.grades i).2 (book S (Pi.single i 1) A) (linearStart A B P (F.grades i).2) := by
  obtain ⟨m,B,hB,P,e,l⟩ := hp i
  exact ⟨m,B,P,hB,fun A=>⟨via_paths S i B P e A,(via_paths S i B P e A).symm ▸ initial_pose A B P _ l⟩⟩
lemma no_lower (S : SectionData F) (hp : Bid.pop S) (i:F.Index) (n : ℕ) (hn:n<(F.grades i).2)
    (A : Links ℤ G.Color) : coeff n (book S (Pi.single i 1) A)=0 := by
  obtain ⟨_,_,_,-,h⟩:=book_start S hp i; exact (h A).2.zero n hn

/-- Engineering horizon d, slot number l. POWERED field symbol, expansion
in g only with nonnegative exponent e; degree l+e in the unscaled link
potential. Not multiplied by its source, or by a length factor. Compare
`C.O` separately with threshold powers and calibrated terminal matrices.
-/
def letter (S : SectionData F) (i : F.Index) (A : Links ℤ G.Color) : PowerSeries ℂ :=
  PowerSeries.mk fun e=> coeff ((F.grades i).2+e) (book S (Pi.single i 1) A)
@[simp] lemma leg_at (S : SectionData F) (i : F.Index) (A : Links ℤ G.Color) (e : ℕ) :
    coeff e (letter S i A) = coeff ((F.grades i).2+e) (book S (Pi.single i 1) A) := coeff_mk ..

theorem powered_letter (S : SectionData F) (hp : Bid.pop S) (i:F.Index) (A : Links ℤ G.Color) :
    letter S i A * PowerSeries.X^(F.grades i).2 = book S (Pi.single i 1) A := by
  ext1 n; rw [coeff_mul_X_pow']; split
  next h=> simp only [leg_at,Nat.add_sub_of_le h]
  next h=> exact (no_lower _ hp _ n (lt_of_not_ge h) _).symm
lemma unit_letter (S : SectionData F) {H} (hp : S.Sound H) (A:Links ℤ G.Color) : letter S 0 A=1 := by
  have he: book S (Pi.single (0:F.Index) 1) A=1 := by rw [← echo_book,show Pi.single (0:F.Index) 1=F.e0 from rfl,hp.unit]; exact ps_one
  ext1 n; rw [leg_at,he,F.zero_degree]; simp

end YM.Dict06.Wil
