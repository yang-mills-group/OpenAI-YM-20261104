import YM.RG11Proof.Rate.Pieces
/-!
# Approximation with payable current-coefficient variations

Fix a degree n>0. A raw regulator `Change` need not BE `Good` (even
constant frame need only be close to leading id; equivariance defects can be
paid at comparison rate). Compare it to the solved partial change at lower
orders, updated at degree n by still unbounded coordinates in the allowed
Lie subspace approximating the raw degree n pieces. Their total l1 cost will
pay all current `Carry`s. These lemmas give concrete operations producing `Unpaid`
rather than supposing that errors multiplying an arbitrary large matrix vanish.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rate
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal Filter
open scoped Topology BigOperators Classical

variable {α J P:Type*} [Fintype J] [DecidableEq J] {shape:P→ℕ} {V:Constraints ℝ J}
variable {k:Budget α} {c d : α→Change ℝ J} {w : α→ℝ} {n : ℕ}
local notation "PS"=> PowerSeries ℝ
/-- Precision class on the finite regulator transformation (not readout). -/
structure OnChange (k : Budget α) (w : α→ℝ) (n : ℕ) (c d : α→Change ℝ J) : Prop where
  parameter : Unpaid k w n (fun a=> (c a).g) (fun a=>(d a).g)
  fields (i j) : Unpaid k w n (fun a=> (c a).Z i j) (fun a=> (d a).Z i j)

omit [DecidableEq J] in
theorem OnChange.response (H : OnChange k w n c d) (hc : ∀ a,Anchored (c a).g) (hd : ∀ a,Anchored (d a).g)
    (hn : 0<n) {A B : α → ArrayAt J ℝ shape} (v : Mark J shape)
    (ha : ∀ i,Pieces k n (fun a=> A a ⟨v.1,i⟩) (fun a=> B a ⟨v.1,i⟩)) :
    Unpaid k w n (fun a=> (c a).act (A a) v) (fun a=> (d a).act (B a) v) :=
  Unpaid.sum Finset.univ fun i _=> Unpaid.mul hn
     (Unpaid.subst_right (ha i) hn H.parameter hc hd)
     (Unpaid.prod Finset.univ hn (fun _ _=> H.fields _ _)) -- method placeholders

/-- Coordinates used for a price step. `none` is the coupling; the finite
entries include unit etc (even those identically zero), so the weight needs no
basis or condition number on the Lie subspace. -/
abbrev Asking (J : Type*) := Option (J×J)

def readOne (V:Constraints ℝ J) (i : Asking J) : Step V →ₗ[ℝ] ℝ :=
  match i with
  | none => LinearMap.snd ℝ _ ℝ
  | some (a,b) => {
        toFun := fun u=> ((u.1:Square J ℝ) a b)
        map_add' _ _:= rfl
        map_smul' _ _:= rfl }

def coins (x : Step V) := ∑ i: Asking J,|readOne V i x|

omit [DecidableEq J] in
@[simp] theorem coins_pos (x : Step V) : 0 ≤ coins x := Finset.sum_nonneg fun _ _=> abs_nonneg _
omit [DecidableEq J] in
theorem burden_step (x : α → Step V) (i : Asking J) : Burden k (fun a=> coins (x a)) (fun a=> readOne V i (x a)) :=
  (Burden.self _ _).dominated (Eventually.of_forall fun a=> by
    rw [abs_of_nonneg (coins_pos _)]; exact Finset.single_le_sum (fun i _=>abs_nonneg (readOne V i (x a))) (Finset.mem_univ _))

/-- Lower-order parts of a raw regulator change approximately calibrated on
reference inputs. Z0≈I exact cost included by choosing p orientation Law. -/
def Older (M : ℕ) (k : Budget α) (c : α→Change ℝ J) (p : Change ℝ J) :=
  (∀ i<M,Near k (fun a=> coeff i (c a).g) (coeff i p.g)) ∧
  (∀ i<M,∀ j l, Near k (fun a=> piece i (c a).Z j l) (piece i p.Z j l))

/-- Update middle reference: use same lower data as p, new Step x at n,
no stipulation on accuracy beyond n. At n>0 lawful. -/
def replace (p : Change ℝ J) (n : ℕ) (x : Step V) : Change ℝ J where
  g := mk fun i=> if i=n then x.2 else coeff i p.g
  Z := unpack fun i=> if i=n then x.1.val else piece i p.Z

omit [DecidableEq J] in
theorem addressed (p : Change ℝ J) (n i) (x : Step V) : coeff i (replace p n x).g = if i=n then x.2 else coeff i p.g := by simp [replace]
omit [DecidableEq J] in
theorem positioned (p : Change ℝ J) (n i) (x : Step V) : piece i (replace p n x).Z = if i=n then x.1.val else piece i p.Z := piece_unpack ..

theorem lawful_replace {p : Change ℝ J} (hp : Law V p) (x : Step V) (hn : 0<n) :
    Law V (replace p n x) := by
  constructor
  · unfold Anchored; rw [← coeff_zero_eq_constantCoeff_apply,addressed,if_neg hn.ne,
    coeff_zero_eq_constantCoeff_apply,hp.1]
  constructor
  · unfold nearId; rw [positioned,if_neg hn.ne,hp.2.baseline]
  intro i hi; rw [positioned]; split
  · exact x.1.property
  exact hp.2.positive hi

-- Allow the raw n coefficients to differ from these candidates by a
-- comparison defect ≤C(1+coins x)E. In particular usable with exact curve &
-- matrices in the allowed variation submodule. If imposing equivariance by
-- averaging, need such quantitative defects to compare to unaveraged outputs.
def Current (V:Constraints ℝ J) (k : Budget α) (c : α→Change ℝ J) (n : ℕ) (x : α→Step V) :=
    let W(a:α):= coins (x a)
    Carry k W (fun a=>coeff n (c a).g) (fun a=>(x a).2) ∧
    ∀ j l, Carry k W (fun a=>piece n (c a).Z j l) (fun a=> (x a).1.val j l)

-- Since E→0, carrying Y from X that itself is at most one factor of
-- (1+W) still costs only one factor, not two.
theorem Carry.bears (W f g : α→ℝ) (h : Carry k W f g) (hh : Burden k W g) : Burden k W f := by
  obtain ⟨C,hc,h⟩:=h; obtain ⟨D,hd,H⟩:=hh; refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,H,k.currency,k.gone.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with a hi he ho hE
  rw [add_mul]
  calc |f a|=|f a-g a+g a|:=by rw [sub_add_cancel]
       _ ≤ |f a-g a| + |g a|:= abs_add_le ..
       _≤ C *_ +_ := add_le_add (hi.trans (by gcongr; nlinarith [show k.E a < 1 from hE])) he

omit [DecidableEq J] in
theorem olderUnpaid (x : α → Step V) (p : Change ℝ J) (h : Older n k c p) (hc : Current V k c n x) :
    OnChange k (fun a=>coins (x a)) n c (fun a=>replace p n (x a)) where
  parameter := {
    lower := fun {m} hm=> by
      constructor
      · intro i hi; exact (h.1 i (hi.trans_lt hm)).bounded
      · intro i hi; simp_rw [addressed,if_neg (hi.trans_lt hm).ne]; exact Bounded.const _
      intro i hi; simp_rw [addressed,if_neg (hi.trans_lt hm).ne]; exact h.1 i (hi.trans_lt hm)
    left :=hc.1.bears _ _ _ (burden_step x none)
    right := by simp_rw [addressed,if_true]; exact burden_step x none
    top := by simp_rw [addressed,if_true]; exact hc.1 }
  fields j l := {
    lower := fun {m} hm=> by
      have he (i m)(hi : i ≤ m)(hm:m < n): i ≠ n:=(hi.trans_lt hm).ne
      constructor
      · intro i hi
        exact (h.2 i (hi.trans_lt hm) j l).bounded
      · intro i hi; simp_rw [← piece_apply j l,positioned,if_neg (he _ _ hi hm)]; exact Bounded.const _
      intro i hi; simp_rw [← piece_apply j l,positioned,if_neg (he _ _ hi hm)]
      exact h.2 i (hi.trans_lt hm) j l
    left := (hc.2 j l).bears _ _ _ (burden_step x (some (j,l)))
    right := by simp_rw [← piece_apply j l,positioned,if_true]; exact burden_step x (some (j,l))
    top := by simp_rw [← piece_apply j l,positioned,if_true]; exact hc.2 j l }
end YM.RG11.Rate
