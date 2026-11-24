import YM.RG11Proof.Rate.Carry

/-!
# Coefficientwise with a still unpaid order

Proofs are all to fixed finite order. `Unpaid k W n` is full rates to orders
STRICTLY below n, with both sizes `Burden k W` and a `Carry k W` rate at n
(no assumption W bounded as k.E → 0). This class is closed under finite
series composition/multiplication at a POSITIVE n; because the nonnegative
power series formulas at that order contain at most one still unpaid factor.
Use for formal regulator errors, not for actual remainders at nonzero coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rate
open PowerSeries YM.RG11.Jets Filter
open scoped Topology Classical BigOperators
local notation "PS" => PowerSeries ℝ
variable {α I : Type*} {k : Budget α} {w : α→ℝ} {p q f g : α→PS} {M N n i : ℕ}

/-- Sizes and regulator comparison simultaneously, so cost closure doesn't
silently assume polynomial bounds on *actual* or comparison objects. -/
structure Pieces (k : Budget α) (M : ℕ) (p q : α→PS) : Prop where
  left {i : ℕ} : i ≤ M → Bounded k (fun a=>coeff i (p a))
  right {i : ℕ} : i ≤ M → Bounded k (fun a=>coeff i (q a))
  price {i : ℕ} : i ≤ M → NearFn k (fun a=>coeff i (p a)) (fun a=>coeff i (q a))

namespace Pieces

theorem tight {p₀ : PS} (h : ∀ i≤M, Near k (fun a=>coeff i (p a)) (coeff i p₀)) : Pieces k M p (fun _=>p₀) :=
  ⟨fun {i} hi=>(h i hi).bounded, fun {_} _=>Bounded.const _,fun {i} hi=>h i hi⟩
@[simp] theorem const (p:PS): Pieces k M (fun _=>p) (fun _=>p):= tight fun _ _=>Near.const _

theorem of_le (he : M ≤ N) (h : Pieces k N p q) : Pieces k M p q :=
  ⟨fun {_} hi=>h.left (hi.trans he),fun {_} hi=>h.right (hi.trans he),fun {_} hi=> h.price (hi.trans he)⟩

theorem mul (H : Pieces k M p q) (hh : Pieces k M f g) : Pieces k M (fun a=>p a*f a) (fun a=>q a*g a) := by
  constructor
  · intro i hi; simp_rw [coeff_mul]
    refine sum_bounded _ (fun b hb=>?_); have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    exact (H.left (by omega)).mul (hh.left (by omega))
  · intro i hi; simp_rw [coeff_mul]
    refine sum_bounded _ (fun b hb=>?_); have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    exact (H.right (by omega)).mul (hh.right (by omega))
  intro i hi; simp_rw [coeff_mul]; refine sum_nearFn _ (fun b hb=>?_); have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hb
  exact (H.price (by omega)).mul (hh.price (by omega)) (H.left (by omega)) (hh.right (by omega))

theorem pow (H : Pieces k M p q) (r:ℕ) : Pieces k M (fun a=>p a^r) (fun a=>q a^r):=by
  induction r with
  | zero=>simp
  | succ r h=>simp_rw [pow_succ]; exact h.mul H

theorem sum {p q:I→α→PS} (s:Finset I) (H:∀ i∈s,Pieces k M (p i) (q i)) : Pieces k M (fun a=>∑ i∈s,p i a) (fun a=>∑ i∈s,q i a):= by
   constructor
   · intro i hi; simp_rw [map_sum]; exact sum_bounded s fun _ h=>(H _ h).left hi
   · intro i hi; simp_rw [map_sum]; exact sum_bounded s fun _ h=>(H _ h).right hi
   intro i hi; simp_rw [map_sum]; exact sum_nearFn s fun _ h=>(H _ h).price hi

theorem add (H : Pieces k M p q) (hh : Pieces k M f g) : Pieces k M (fun a=>p a+f a) (fun a=>q a+g a) := by
  constructor
  · intro i hi; simp_rw [map_add]; exact (H.left hi).add (hh.left hi)
  · intro i hi; simp_rw [map_add]; exact (H.right hi).add (hh.right hi)
  intro i hi; simp_rw [map_add]; exact (H.price hi).add (hh.price hi)

theorem neg (H : Pieces k M p q) : Pieces k M (fun a=> -p a) (fun a=> -q a) := by
  constructor
  · intro i hi; simp_rw [map_neg]; exact (H.left hi).neg
  · intro i hi; simp_rw [map_neg]; exact (H.right hi).neg
  intro i hi; simp_rw [map_neg]; exact (H.price hi).neg

theorem sub (H : Pieces k M p q) (hh : Pieces k M f g) : Pieces k M (fun a=>p a-f a) (fun a=>q a-g a) := by simp_rw [sub_eq_add_neg]; exact H.add hh.neg

theorem congr (H : Pieces k M p q) (hp : p =ᶠ[k.along] f) (hq : q =ᶠ[k.along] g): Pieces k M f g := by
  constructor
  · intro i hi; exact Bounded.dominate (H.left hi) (hp.mono fun _ hw=> by rw [hw])
  · intro i hi; exact Bounded.dominate (H.right hi) (hq.mono fun _ hw=> by rw [hw])
  intro i hi; exact NearFn.congr (H.price hi) (hp.mono fun _ hw=>by dsimp; rw [hw]) (hq.mono fun _ hw=>by dsimp; rw [hw])

-- For use at lower orders or already bounded changes.
theorem compose (H : Pieces k M p q) (hh : Pieces k M f g) (h₁ : ∀ a, Anchored (f a)) (h₂ : ∀ a, Anchored (g a)) :
    Pieces k M (fun a=>PowerSeries.subst (f a) (p a)) (fun a=>PowerSeries.subst (g a) (q a)) := by
  constructor
  · intro i hi; simp_rw [coeff_compose _ _ _ (h₁ _)]
    exact sum_bounded _ (fun j hj=> (H.left ((show j ≤ i by simp at hj; omega).trans hi)).mul ((hh.pow j).left hi))
  · intro i hi; simp_rw [coeff_compose _ _ _ (h₂ _)]
    exact sum_bounded _ (fun j hj=> (H.right ((show j ≤ i by simp at hj; omega).trans hi)).mul ((hh.pow j).right hi))
  intro i hi; simp_rw [coeff_compose _ _ _ (h₁ _),coeff_compose _ _ _ (h₂ _)]
  refine sum_nearFn _ (fun j hj=> ?_); have he : j≤M := by rw [Finset.mem_range] at hj; omega
  exact (H.price he).mul ((hh.pow j).price hi) (H.left he) ((hh.pow j).right hi)
end Pieces

/-- For applications typically choose n positive. The reference q may
include unknown coefficients too (e.g. compare the same unknown order-n field
change acting on approximate free arrays to its action on exact free arrays).
-/
structure Unpaid (k : Budget α) (w : α→ℝ) (n : ℕ) (p q : α→PS) : Prop where
  lower {m : ℕ} : m<n → Pieces k m p q
  left : Burden k w (fun a=>coeff n (p a))
  right : Burden k w (fun a=>coeff n (q a))
  top : Carry k w (fun a=>coeff n (p a)) (fun a=>coeff n (q a))

namespace Unpaid

theorem of_pieces (w : α→ℝ) (h : Pieces k n p q) : Unpaid k w n p q :=
  ⟨fun {_} hi=> h.of_le hi.le,Burden.of_bounded (h.left le_rfl),Burden.of_bounded (h.right le_rfl),NearFn.carry (h.price le_rfl) _⟩ -- dot of_le signature?
@[simp] theorem const (t : PS) : Unpaid k w n (fun _=>t) (fun _=>t):= of_pieces _ (Pieces.const _)

theorem finishes (h : Unpaid k w n p q) (hw : Bounded k w) : Pieces k n p q:= by
  obtain ⟨W,hW,hk⟩:=hw
  have he (f) (h : Burden k w f):Bounded k f:= by
    obtain ⟨C,hc,H⟩:=h; refine ⟨C*(1+W),by positivity,?_⟩; filter_upwards [H,hk] with a hp hi; apply hp.trans; gcongr
  constructor
  · intro i hi; obtain hh|rfl:=lt_or_eq_of_le hi; · exact (h.lower hh).left le_rfl
    exact he _ h.left
  · intro i hi; obtain hh|rfl:=lt_or_eq_of_le hi; · exact (h.lower hh).right le_rfl
    exact he _ h.right
  intro i hi; obtain hh|rfl:=lt_or_eq_of_le hi; · exact (h.lower hh).price le_rfl
  exact h.top.boundedWeight ⟨_,hW,hk⟩

-- For ease/speed use combined proof for multiplication upper terms.
private theorem crest (hn:0<n) (H : Unpaid k w n p q) (hh : Unpaid k w n f g) (z : ℕ×ℕ) (hz : z.1+z.2=n) :
    let x (a:α) := coeff z.1 (p a)*coeff z.2 (f a)
    let y (a:α) := coeff z.1 (q a)*coeff z.2 (g a)
    Burden k w x ∧ Burden k w y ∧ Carry k w x y := by
  intro x y
  obtain hZ|hZ := lt_or_ge z.1 n
  · have hA := H.lower hZ
    obtain hY|hY := lt_or_ge z.2 n
    · have hB:=hh.lower hY
      have hf:= (hA.left (i:=z.1) le_rfl).mul (hB.left (i:=z.2) le_rfl)
      have hg:= (hA.right (i:=z.1) le_rfl).mul (hB.right (i:=z.2) le_rfl)
      have h:= (hA.price le_rfl).mul (hB.price le_rfl) (hA.left le_rfl) (hB.right le_rfl)
      exact ⟨Burden.of_bounded hf,Burden.of_bounded hg,h.carry w⟩
    have he : z.2=n:=by omega
    unfold x y; rw [he]
    have h:= hh.top.mul_right hh.right (hA.price le_rfl) (hA.left le_rfl)
    exact ⟨hh.left.mult_left (hA.left le_rfl),hh.right.mult_left (hA.right le_rfl),h⟩
  have he : z.1=n:=by omega
  have hj : z.2=0:=by omega
  unfold x y; rw [he,hj]
  have hB:=hh.lower hn
  have h:=H.top.mul_left H.right (hB.price le_rfl) (hB.left le_rfl)
  exact ⟨H.left.mult_right (hB.left le_rfl),H.right.mult_right (hB.right le_rfl),h⟩

theorem mul (hn : 0<n) (H : Unpaid k w n p q) (hh : Unpaid k w n f g) : Unpaid k w n (fun a=>p a*f a) (fun a=>q a*g a):= by
  constructor
  · intro i hi; exact (H.lower hi).mul (hh.lower hi)
  · simp_rw [coeff_mul]; exact burden_sum (fun z hz=> (crest hn H hh z (Finset.HasAntidiagonal.mem_antidiagonal.mp hz)).1)
  · simp_rw [coeff_mul]; exact burden_sum (fun z hz=> (crest hn H hh z (Finset.HasAntidiagonal.mem_antidiagonal.mp hz)).2.1)
  simp_rw [coeff_mul]; exact carry_sum (fun z hz=> (crest hn H hh z (Finset.HasAntidiagonal.mem_antidiagonal.mp hz)).2.2)

theorem pow (hn : 0<n) (H : Unpaid k w n p q) (r:ℕ) : Unpaid k w n (fun a=> p a^r) (fun a=> q a^r):= by
  induction r with
  | zero=> simp
  | succ r ih=> simpa only [pow_succ] using ih.mul (by omega) H -- .mul dot work?

theorem sum {p q : I→α→PS} (s:Finset I) (H:∀ i∈s,Unpaid k w n (p i) (q i)) : Unpaid k w n (fun a=>∑ i∈s,p i a) (fun a=>∑ i∈s,q i a) := by
  constructor
  · intro m hm; exact Pieces.sum s (fun i h=>(H _ h).lower hm)
  · simp_rw [map_sum]; exact burden_sum (fun i hi=>(H i hi).left)
  · simp_rw [map_sum]; exact burden_sum (fun i hi=>(H i hi).right)
  simp_rw [map_sum]; exact carry_sum fun i hi=>(H i hi).top

theorem prod {p q : I→α→PS} (s:Finset I) (hn : 0<n) (H : ∀ i∈s,Unpaid k w n (p i) (q i)) : Unpaid k w n (fun a=>∏ i∈s,p i a) (fun a=>∏ i∈s,q i a):= by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih=>
     simp_rw [Finset.prod_insert hi]; exact (H i (by simp)).mul hn (ih (fun j hj=>H j (by simp [hj])))

theorem add (H : Unpaid k w n p q) (hh : Unpaid k w n f g) : Unpaid k w n (fun a=>p a+f a) (fun a=>q a+g a) := by
  constructor
  · intro i hi; exact (H.lower hi).add (hh.lower hi)
  · simp_rw [map_add]; exact H.left.add hh.left
  · simp_rw [map_add]; exact H.right.add hh.right
  simp_rw [map_add]; exact H.top.add hh.top

theorem neg (H : Unpaid k w n p q) : Unpaid k w n (fun a=> -p a) (fun a=> -q a) := by
  constructor
  · intro i hi; exact (H.lower hi).neg
  · simp_rw [map_neg]; exact H.left.neg
  · simp_rw [map_neg]; exact H.right.neg
  simp_rw [map_neg]; exact H.top.neg

theorem sub (H : Unpaid k w n p q) (hh : Unpaid k w n f g) : Unpaid k w n (fun a=>p a-f a) (fun a=>q a-g a) := by simp_rw [sub_eq_add_neg]; exact H.add hh.neg

-- Careful: **outer and inner cannot both be Unpaid if inner tangent may be
-- unknown and n=1**. More generally with n>1 can extend by using the anchored
-- condition and powers to track leading tangent, but for our use the outer
-- series all have coefficients paid.
theorem subst_right (H : Pieces k n p q) (hn : 0<n) (hh : Unpaid k w n f g) (hf : ∀ a,Anchored (f a)) (hg : ∀ a,Anchored (g a)) :
    Unpaid k w n (fun a=>PowerSeries.subst (f a) (p a)) (fun a=>PowerSeries.subst (g a) (q a)) := by
  constructor
  · intro m hm; exact (H.of_le hm.le).compose (hh.lower hm) hf hg
  · simp_rw [coeff_compose _ _ _ (hf _)]
    refine burden_sum (fun i hi=> ((hh.pow hn i).left).mult_left ?_)
    exact H.left (by simp at hi;omega)
  · simp_rw [coeff_compose _ _ _ (hg _)]
    refine burden_sum (fun i hi=> ((hh.pow hn i).right).mult_left ?_)
    exact H.right (by simp at hi;omega)
  simp_rw [coeff_compose _ _ _ (hf _),coeff_compose _ _ _ (hg _)]
  refine carry_sum (fun i hi=> ?_); have he : i≤n:=by simp at hi; omega
  exact ((hh.pow hn i).top).mul_right ((hh.pow hn i).right) (H.price he) (H.left he)
end Unpaid
end YM.RG11.Rate
