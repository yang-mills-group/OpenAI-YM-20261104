import YM.RG11Proof.Jets.Detector

/-!
# Calibration of a change between two systems at a finite field horizon

After orientation at zeroth order, construct ALL-orders finite-demand coherent
formal symbols `solution D B` by solving only a square system of separated
tests. The leading **coupling tangent is solved too**, not assumed. A calibration
equation at positive order holds without the rest of the correlation arrays
matching; the latter means solving ALSO the invariants (defects orthogonal to
the joint pencil), for which we need regulator/physical estimates, covered by
other files. This gives finite uniqueness for H_restrict and compact-regulator
passages later.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RG11.Formal
open PowerSeries YM.RG11.Jets YM.PertExtension.Position
open scoped BigOperators

variable {R J P : Type*} [Field R] [Fintype J] [DecidableEq J]
variable {shape:P→ℕ} {A : ArrayAt J R shape} {L : Constraints R J}

-- Near-identity field law and a possibly singular ruler until first order identified
def Law (L : Constraints R J) (c : Change R J) := Anchored c.g ∧ L.Lawful c.Z
/-- Coefficient read as a variation. -/
def seen (c : Change R J) (h : Law L c) (n : ℕ) (hn : 0<n) : Step L :=
  (⟨piece n c.Z,h.2.positive hn⟩, coeff n c.g)

-- A frame and coupling with the latter pinned always at zero at order zero.
-- This does not divide by an unknown tangent in constructing a unique ruler.
def seed (R J : Type*) [Field R] [DecidableEq J] : Change R J := ⟨0,1⟩
theorem seed_law : Law L (seed R J) :=
  ⟨Anchored.empty,Constraints.Lawful.id⟩

def fromStep (f : ℕ → Step L) : Change R J where
  g := mk fun i=> if i=0 then 0 else (f i).2
  Z := unpack fun i=> if i=0 then 1 else (f i).1.val

theorem fromStep_law (f : ℕ→Step L) : Law L (fromStep f) := by
  refine ⟨(by simp [Anchored,fromStep]),(by
    constructor
    · unfold nearId; simp [fromStep]
    intro i hi; simp only [fromStep,piece_unpack, if_neg hi.ne']; exact (f i).1.property)⟩

@[simp] theorem seen_fromStep (f : ℕ→Step L) (n : ℕ) (hn : 0<n) :
    seen (fromStep f) (fromStep_law f) n hn=f n := by ext <;> first | (simp [seen,fromStep, hn.ne', unpack])

theorem ext_law_through {c d : Change R J} (hc : Law L c) (hd : Law L d) {m}
    (h : ∀ i (hi:0 < i), i ≤ m → seen c hc i hi=seen d hd i hi) : Change.EquivJet c d m := by
  constructor
  · intro i he
    cases i with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,hc.1,hd.1]
    | succ i => exact congrArg Prod.snd (h _ (by omega) he)
  apply MatThrough.of_piece; intro i hi
  cases i with
  | zero => rw [hc.2.baseline, hd.2.baseline]
  | succ i => exact congrArg (fun k:Step L=> (k.1:Square J R)) (h _ (by omega) hi)

theorem ext_law {c d : Change R J} (hc : Law L c) (hd : Law L d)
    (h : ∀ i (hi:0 < i), seen c hc i hi=seen d hd i hi) : c=d := by
  have H(n) := ext_law_through (m:=n) hc hd (fun i hi _=> h i hi)
  ext <;> first | exact (H _).ruler _ le_rfl | exact (H _).field _ _ _ le_rfl

/-- Solver with input reference array `A`, uses only finite D.test to paint
positive coefficients. Centering encoded for rulers later. -/
def entries (D : Detector L A) (B : ArrayAt J R shape) (n : ℕ) : Step L :=
  if n=0 then 0
  else
    let prev := fromStep (fun i=> if _:i<n then entries D B i else 0)
    D.restore fun i=> coeff n (B (D.test i)) - coeff n (prev.act A (D.test i))
termination_by n

def solution (D : Detector L A) (B : ArrayAt J R shape) : Change R J :=
  fromStep (entries D B)

theorem solution_law (D : Detector L A) (B : ArrayAt J R shape) : Law L (solution D B) := fromStep_law _

/-- Position/ruler calibration: after transform, the fixed linear combinations
of test deviations at *positive* order must vanish. Need same leading array
separately. -/
def price (D : Detector L A) (B : ArrayAt J R shape) (n : ℕ) : Step L :=
    D.restore (fun i=> coeff n (B (D.test i)))

def Hits (D : Detector L A) (B : ArrayAt J R shape) (c : Change R J) (n : ℕ) :=
  price D B n=price D (c.act A) n

theorem pays_diff (D : Detector L A) {c d : Change R J} (hc : Law L c) (hd : Law L d) {n:ℕ} (hn : 0<n)
    (H : ∀ i (hi:0 < i), i<n → seen c hc i hi=seen d hd i hi) :
    price D (c.act A) n + (seen d hd n hn - seen c hc n hn) = price D (d.act A) n := by
  let x := seen d hd n hn - seen c hc n hn
  have he (w : Mark J shape) : coeff n (c.act A w) + fullRead L A x w=coeff n (d.act A w) := by
    have he (i) (hi : i<n):= ext_law_through (m:=i) hc hd (fun i h j=> H i h (j.trans_lt hi))
    exact (pencil_action (A:=A) hn hc.1 hc.2.baseline (X:=x.1.val) (c:=x.2) (strike_minus_of_prior fun i hi=> (he i hi).ruler i le_rfl) (fun i j=>
        strike_minus_of_prior fun k hk=> (he k hk).field i j k le_rfl) w).value
  unfold price
  rw [show seen d hd n hn - _=x from rfl, ← D.works x] -- also rewrites inside?
  rw [← map_add]; exact congrArg D.restore (funext fun i=> he (D.test i))

theorem hits (D : Detector L A) (B : ArrayAt J R shape) {n:ℕ} (hn:0<n) :
    Hits D B (solution D B) n := by
  let f := fun i=> if _:i<n then entries D B i else 0
  let p := fromStep f
  have hD : Law L p:=fromStep_law f
  have hEq i (hi:0 < i) (hh:i<n) : seen p hD i hi = seen (solution D B) (solution_law D B) i hi := by
    simp only [solution,p,seen_fromStep,f,dif_pos hh]
  have h := pays_diff D hD (solution_law D B) hn hEq
  simp only [p,solution,seen_fromStep, f,dif_neg (lt_irrefl n),sub_zero] at h
  have he : entries D B n = price D B n-price D (p.act A) n := by
    conv_lhs => rw [entries,if_neg hn.ne']
    simp only [price,← map_sub]; rfl
  rw [he] at h
  unfold Hits solution
  rw [←h, show fromStep (fun i=> if _:i<n then entries D B i else 0)=p from rfl, add_sub_cancel]

theorem uniqueness (D : Detector L A) (B : ArrayAt J R shape) {c d : Change R J}
    (hc : Law L c) (hd : Law L d) (n)
    (h : ∀ i≤n,0 < i → Hits D B c i)
    (j : ∀ i≤n,0 < i → Hits D B d i) : Change.EquivJet c d n := by
  apply ext_law_through hc hd
  intro i hi hp
  induction i using Nat.strong_induction_on with
  | _ i hI =>
    have hK:= pays_diff D hc hd hi (fun m hm hmi=> hI m hmi hm (by omega))
    rw [← h i hp hi, ← j i hp hi] at hK
    exact (sub_eq_zero.mp (add_eq_left.mp hK)).symm

theorem unique (D : Detector L A) (B : ArrayAt J R shape) {c : Change R J}
    (hc : Law L c) (h : ∀ i,0 < i → Hits D B c i) : c=solution D B := by
  have he (n):= uniqueness D B hc (solution_law D B) n (fun i _=>h i) (fun _ _=>hits D B)
  ext <;> first|exact (he _).ruler _ le_rfl|exact (he _).field _ _ _ le_rfl

/-- The finite number of additional order-one inputs needed for the tangent
of the solved change. No coupling inverse needed. -/
theorem tangent_solution (D : Detector L A) (B : ArrayAt J R shape) :
   tangent (solution D B).g = (D.restore (fun i=> coeff 1 (B (D.test i)))).2 := by
  let p := fromStep (fun i => if _:i<1 then entries D B i else 0)
  have h₀ : p = seed R J := by
    apply ext_law (fromStep_law (L:=L) _) (seed_law (L:=L))
    intro i h
    ext <;> simp [seen, seed,fromStep,unpack,h.ne']
  unfold tangent solution
  rw [fromStep, PowerSeries.coeff_mk, if_neg (by decide)]
  change (entries D B 1).2 = _
  have he v : coeff 1 ((seed R J).act A v)=0 := by
    unfold Change.act seed
    simp_rw [PowerSeries.subst_zero_eq_C_constantCoeff]
    convert! congrArg (coeff 1) (insert_one (fun w=> PowerSeries.C (constantCoeff (A w))) v)
    · simp [Matrix.one_apply]
    simp
  rw [entries,if_neg (by decide)]; change (D.restore (fun i=> _-coeff 1 (p.act A (D.test i)))).2= _
  simp_rw [h₀,he,sub_zero]
end YM.RG11.Formal
