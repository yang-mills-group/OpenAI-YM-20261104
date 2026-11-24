import YM.GradedFar.Continuation.Insert

/-!
# First-line accuracy at the true Far columns

Argument for the full row; applies in precisely the same way to
all singleton rows. Explicit calls to (G.9) and (G.1)-type conditions. This is an
internal lemma; actual application uses the actual operands.
-/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ} {e : Fin m → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

abbrev ReadAt (G : Gauge) {n m : ℕ} (d : Fin n → ℕ) (e : Fin m → ℕ) (I : Type) :=
  Window → I → Points n → Points m → Inputs G d → MultilinearMap ℂ (fun i => Sec G (e i)) ℂ
abbrev ChangeAt (G : Gauge) := (d : ℕ) → Window → Module.End ℂ (Sec G d)
def Coat (Z : ChangeAt G) (w : Window) (v : Inputs G e) : Inputs G e := fun i => Z (e i) w (v i)
/-- Literal through-k crop of a `Kseries` column. (Use before applying G.1.) -/
def atColumn (x : Guard G n) (k : ℕ) (t : ℝ) : Module.End ℂ (Sec G n) :=
  ∑ j ∈ Finset.range (k+1), (t:ℂ)^j • coeff j x
lemma col_money (x : Guard G n) (k : ℕ) (t : ℝ) (v : Sec G n) (c : Toon G n) :
    coord c (atColumn x k t v) = crop k t (mode (fun j => coeff j x v) c) := by
  unfold atColumn mode; simp only [crop_eq]; rw [LinearMap.sum_apply]; simp_rw [LinearMap.smul_apply,map_sum,_root_.map_smul,smul_eq_mul,coeff_mk]

/-- Using the same coordinate sup norm throughout (and can prove the hypothesis with
any fixed equivalent norm). Take L=1. -/
def Ball (L : ℝ) (v : Sec G n) : Prop := ∀ b, ‖coord b v‖≤ L
lemma ball_basis (b : Toon G n) : Ball 1 (theory b) := by
  intro c; rw [pivotδ]; split <;> simp
lemma within_basis (v : Choices G d) : Within 1 (basisInputs v) :=
  fun i => ball_basis (v i)

local notation "g" => gYM G
section
variable (Z : ChangeAt G) (Q : Set Window) (t : ℝ → ℝ) (p : ℕ)
/-- Receipted formula for the G.1 field hypothesis of the growing comparison (the part
actually used). Component norm convention; `atColumn ... k'` through an order sufficiently
high to buy even g^(p+2). On the windows Q. -/
def ReplacementAt (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (n : ℕ) (Z : ChangeAt G)
    (Q : Set Window) (t : ℝ → ℝ) (p : ℕ) : Prop :=
  ∀ L : ℝ, ∃ k' : ℕ, p+5 ≤ k' ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ w in windows Q, ∀ v : Sec G n, Ball L v →
      Ball (C*g w.len^(p+2)) (Z n w v - atColumn (Kseries N M n (-w.sep)) k' (t w.len) v)

variable {I : Type} (F0 : ReadAt G d e I)
  {K : Set (Points n)} {S : Set (Points m)}

/-- G.9 input (for the arithmetic); true row with all r labels against the raw prediction through p. -/
def RoundedAt (N : WilsonPrescription G) (F : ReadAt G d e I) (Q : Set Window) (K : Set (Points n))
    (S : Set (Points m)) (t : ℝ → ℝ) (p : ℕ) : Prop := ∀ L R : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
      ∀ᶠ w in windows Q, ∀ i x, x∈K → ∀ y ∈ S, ∀ u : Inputs G d, Within L u →
      ∀ v : Inputs G e, Within R v → ‖F w i x y u v-crop p (t w.len) (row N x u y v w.sep)‖ ≤
        C*g w.len^(p+1)*(1+w.sep)^a

/-- Output shape (M2.1), in the physical stretch T. Here just a single full-row
call. -/
def WithinError (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (F0 : ReadAt G d e I)
    (Z : ChangeAt G) (Q : Set Window) (K : Set (Points n)) (S : Set (Points m)) (t : ℝ → ℝ)
    (p : ℕ) (L R : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ w in windows Q, ∀ i x, x∈K → ∀ y ∈ S, ∀ u : Inputs G d, Within L u →
      ∀ v : Inputs G e, Within R v →
        ‖F0 w i x y u (Coat Z w v)-crop p (t w.len) (Yx N M x y u v w.sep)‖ ≤
          C*w.Stretch^(∑ j, e j)*g w.len^(p+1) * (1+w.sep)^a

variable (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
include H hK hx hS hy
/-- Arithmetic extraction of `WithinError`. -/
theorem paid_first (ht : ∀ᶠ r in 𝓝[>] (0:ℝ), |t r| ≤ 2*g r)
    (hA : ∀ j, ReplacementAt N M (e j) Z Q t p)
    (hF : RoundedAt N F0 Q K S t p) (L R : ℝ) : WithinError N M F0 Z Q K S t p L R := by
  let X := Window × I × ↥K × ↥S × {u : Inputs G d // Within L u} × {v : Inputs G e // Within R v}
  let w (i : X) := i.1
  let x (i : X) := i.2.2.1; let y (i : X) := i.2.2.2.1
  let u (i : X) := i.2.2.2.2.1.val; let v (i : X) := i.2.2.2.2.2.val
  let W i := Coat Z (w i) (v i)
  have hu (i : X) : Within L (u i) := i.2.2.2.2.1.property
  have hv (i : X) : Within R (v i) := i.2.2.2.2.2.property
  let b := pack (boarded simple Q) w
  have hw : Tendsto w b.l (windows Q) := tendsto_comap
  let t0 i := t (w i).len
  have H0 : ∀ᶠ i in b.l, |t0 i| ≤ 2*b.g i := ((windows_short Q).comp hw).eventually ht
  let F (i : X) := F0 i.1 i.2.1 (x i).val (y i).val (u i)
  have HA (c : Choices G e) (j) : ∃ k' : ℕ, p+5 ≤ k' ∧ Bill b (p+2) 0 (fun i =>
        coord (c j) (W i j) - crop k' (t0 i) (mode (exterior N M (-b.s i) (v i) j) (c j))) := by
    obtain ⟨k,hk,C,hC,hA⟩ := hA j R
    refine ⟨k,hk,C,hC,0,?_⟩
    filter_upwards [hw.eventually hA] with i hi
    have hu := hi (v i j) (hv i j) (c j)
    rw [map_sub,col_money] at hu
    rw [post,neg_zero,zero_mul,exp_zero,pow_zero,mul_one,mul_one]; exact hu
  have Hφ (c : Choices G e) : Bill b (p+1) 0 (fun i => F i (basisInputs c)-
        crop p (t0 i) (row N (x i).val (u i) (y i).val (basisInputs c) (b.s i))) := by
    obtain ⟨C,hC,a,hφ⟩ := hF L 1
    refine ⟨C,hC,a,?_⟩
    filter_upwards [hw.eventually hφ] with i hi
    rw [post,neg_zero, zero_mul,exp_zero,mul_one]
    exact hi _ _ (x i).property _ (y i).property _ (hu i) _ (within_basis c)
  obtain ⟨C,hC,a,hm⟩ := true_pay H v W hv H0 p HA hK hx hS hy x y u hu F Hφ
  refine ⟨C,hC,a,?_⟩
  filter_upwards [eventually_comap.mp hm] with k hk i xr pX yr pY U pU V pV
  obtain he := hk ((k,i,⟨xr,pX⟩,⟨yr,pY⟩,⟨U,pU⟩,⟨V,pV⟩):X) rfl
  let D := ∑ j, e j
  apply he.trans_eq
  change C*g k.1^(p+1)*post (-(D:ℝ)) k.2 a=C*(exp k.2)^D*g k.1^(p+1)*(1+k.2)^a
  rw [post,neg_neg,exp_nat_mul]; ring
end
end
end YM.FVA2.GradedFar.Continuation
