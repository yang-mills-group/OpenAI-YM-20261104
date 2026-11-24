import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Compact
/-!
# Complete the 'all orders above p' budget, also for crops within all Far legs

The *second* inequality uses whole `D^X` & `Y^X` and only at the product with c
needs to recrop (estimate purchased in `Formal`). To also compare with the actual
physical fields toward M.3 one needs to know the cost of forming **each Far leg's
finite polynomial**, even on this same T scale. Prove the additional payment.
It will enter the use of physical G.1 and G.9 (not conclusions of this file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O.Score O.Enh O.Canon PowerSeries
open XSpace XSpace.Normalize Dframe
open scoped Topology Classical BigOperators

variable {G : Gauge} {n m h p q H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (V : Arenas G)

/-- RAW formal price -- no transfer in this order-p summation. Used on
all-H_r moment comparisons via their input Sec labels. -/
def unconverted (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (u : Appointed122Fields G d) (v : Appointed122Fields G e) : PowerSeries ℂ :=
  PowerSeries.mk fun k => mix V z k hd he (fun _ => 1) u v
lemma unconverted_coeff (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (u : Appointed122Fields G d) (v : Appointed122Fields G e) (k : ℕ) : coeff k (unconverted V z hd he u v) =
    mix V z k hd he (fun _ => 1) u v := coeff_mk ..

variable (B : ℝ → Frames G) (η : ℝ) (z : Points (n+m))
    (hd : Covered d H) (he : Covered e H) (u : Appointed122Fields G d) (v : Appointed122Fields G e)
    (p q : ℕ) (t : ℂ)

/-- The separately cropped `K` at order q, which may be much larger than p. T fixed. -/
def croppedTransfer (d : ℕ) : FieldEnd G d := ∑ i : Fin (q+1), t^i.val • coeff i.val (transfer B η d)

def preapply (r : ∀ i, FieldEnd G (e i)) (v : Appointed122Fields G e) : Appointed122Fields G e := fun i => r i (v i)

def applied (B : ℝ → Frames G) (η : ℝ) (v : Appointed122Fields G e) (q : ℕ) (t : ℂ) :=
  preapply (fun i => croppedTransfer B η q t (e i)) v

lemma applied_def (j : Fin m) : applied B η v q t j =
    ∑ i : Fin (q+1), t^i.val • coeff i.val (transfer B η (e j)) (v j) := by
  simp only [applied, preapply,croppedTransfer, LinearMap.sum_apply, LinearMap.smul_apply]

abbrev PayP (p q m : ℕ) := Fin (p+1) × (Fin m → Fin (q+1))
def allDay (p q m : ℕ) : PayP p q m ↪ Days m where
  toFun i := Finsupp.equivFunOnFinite.symm (fun a => a.elim i.1.val (fun j => (i.2 j).val))
  inj' i j h := by
    have H := Finsupp.equivFunOnFinite.symm.injective h
    exact Prod.ext (Fin.ext (congrFun H none)) (funext (fun k => Fin.ext (congrFun H (some k))))
abbrev allPower (u : Days m) := ∑ i, u i

private lemma pays (F : Days m → ℂ) (h : p ≤ q) :
    ∑ i ∈ Finset.range (p+1), ∑ u ∈ tally i m, F u =
      ∑ u ∈ Finset.univ.filter (fun u : PayP p q m => allPower (allDay p q m u) ≤ p), F (allDay p q m u) := by
  let A := Finset.range (p+1); let J := (fun i => tally i m); let W := A.biUnion J
  let D := allDay p q m
  have H u : u∈W ↔ allPower u ≤ p := by
    simp only [W,A,J,Finset.mem_biUnion,Finset.mem_range,Nat.lt_succ_iff,totaled]
    exact ⟨fun ⟨t,ht,h⟩ => h.trans_le ht, fun h => ⟨_,h,rfl⟩⟩
  have covered u (h':u∈W) : ∃ i, u = D i := by
    have b i : u i ≤ p := (Finset.single_le_sum (f:=fun i => u i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)).trans ((H u).mp h')
    refine ⟨(⟨u none,Nat.lt_succ_of_le (b _)⟩,fun i => ⟨u (some i), Nat.lt_succ_of_le ((b _).trans h)⟩),?_⟩
    ext (i|i) <;> rfl
  have eq : W = Finset.map D (Finset.univ.filter (fun i => allPower (D i) ≤ p)) := by
    ext u; simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor; · intro hu; obtain ⟨i,rfl⟩ := covered u hu; exact ⟨i,(H _).mp hu,rfl⟩
    rintro ⟨i,hi,rfl⟩; exact (H _).mpr hi
  change (∑ i ∈ A, ∑ u ∈ J i, F u)=_
  rw [← Finset.sum_biUnion]
  · change (∑ u∈W,F u)=_; rw [eq,Finset.sum_map]
  intro i _ j _ ne; exact Finset.disjoint_left.mpr (fun s h₁ h₂ => ne (((totaled s).mp h₁).symm.trans ((totaled s).mp h₂)))

/-- The coefficient term contributed by all of this exact set of allocations. -/
def orderedTerm (w : Days m) : Form G d (Form G e ℂ) :=
  mix V z (w none) hd he fun i => coeff (w (some i)) (transfer B η (e i))

lemma postCrop : filedCrop122 p t (unconverted V z hd he u (applied B η v q t)) =
    ∑ i : PayP p q m, orderedTerm V B η z hd he (allDay p q m i) u v * t^allPower (allDay p q m i) := by
  rw [filedCropEq122, ← Fin.sum_univ_eq_sum_range _ (p+1), Fintype.sum_prod_type];
  refine Finset.sum_congr rfl fun i _ => ?_; rw [unconverted_coeff]
  let X := mix V z i.val hd he (fun _ => 1) u
  change X (applied B η v q t) * t^i.val = _
  rw [show applied B η v q t = (fun j => _) from funext (applied_def B η v q t),
    MultilinearMap.map_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
  unfold X; rw [MultilinearMap.map_smul_univ]; simp only [smul_eq_mul]
  let w := allDay p q m (i,j)
  have hP : allPower w = i.val + ∑ u : Fin m, (j u).val := Fintype.sum_option _
  change _ = orderedTerm V B η z hd he w u v * _
  rw [Finset.prod_pow_eq_pow_sum, mul_comm (_^_), mul_assoc, ← pow_add,
    add_comm (Finset.sum _ _), hP, mix_apply, orderedTerm, mix_apply ]; rfl

lemma preCrop : filedCrop122 p t (series V B η z hd he u v) =
    ∑ i∈Finset.range (p+1), ∑ w∈tally i m,
      orderedTerm V B η z hd he w u v * t^allPower w := by
  simp_rw [filedCropEq122, series_coeff, ordered, _root_.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (fun w hw => by
    rw [show allPower w = _ from (totaled w).mp hw]; rfl)

def overCosts (p q m : ℕ) := Finset.univ.filter (fun u : PayP p q m => ¬ allPower (allDay p q m u) ≤ p)

/-- Shifted sum of omitted terms. -/
def preBill : Form G d (Form G e ℂ) :=
  ∑ w∈overCosts p q m, t^(allPower (allDay p q m w) - (p+1)) •
    orderedTerm V B η z hd he (allDay p q m w)

lemma recropping (h : p ≤ q) : filedCrop122 p t (unconverted V z hd he u (applied B η v q t)) =
    filedCrop122 p t (series V B η z hd he u v) + preBill V B η z hd he p q t u v * t^(p+1) := by
  let W (u:PayP p q m) := allDay p q m u
  rw [postCrop, preCrop, pays _ _ _ h, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : PayP p q m => allPower (W i) ≤ p)]
  congr 1; unfold preBill; simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Finset.sum_mul];
  refine Finset.sum_congr rfl fun i hi => ?_
  have hp : p+1 ≤ allPower (W i) := Nat.succ_le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
  rw [mul_comm (t^(_-_)), mul_assoc, ← pow_add, Nat.sub_add_cancel hp]
end YM.FVA2.GradedFar
