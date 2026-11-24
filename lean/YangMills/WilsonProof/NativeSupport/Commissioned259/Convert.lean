import YangMills.WilsonProof.NativeSupport.Commissioned259.Row

/-! # Expand every one of the K columns, in the all-horizon physical alphabet -/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Rake MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe

variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m H : ℕ} (L : Law V R B)

/-- Only the same grade appears; factor out the exact power of T specified in the proof.
`bead B η b j` stays log-polynomial! -/
abbrev bead (B : ℝ → Frames G) (η : ℝ) (b : Q G) (j : Grade G (heft b)) : PowerSeries ℂ :=
  cue (seats (B η)) b (own j)

def columnEntry (B : ℝ → Frames G) (η : ℝ) (b : Q G) (j : Grade G (heft b)) : PowerSeries ℂ :=
  PowerSeries.C (Extent.token η (heft b)) * bead B η b j

section Column
include L
lemma same_grade (η : ℝ) (b : Q G) (hb : heft b ≤ H) (k : ℕ) :
    coeff k (conversion B η H) (cap b hb) = ∑ j : Grade G (heft b),
      coeff k (columnEntry B η b j) • cap (own j) (d:=H) hb := by
  rw [coeff_conversion, cap_map (slot L η), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.map_smul, cap, Level.exact₀, low_size, smul_smul, mul_comm,
    columnEntry, coeff_C_mul]

omit L in
lemma power_T (b : Q G) (k : ℕ) (j : Grade G (heft b)) {T : ℝ} (hT : 0 < T) :
    coeff k (columnEntry B (-Real.log T) b j) =
      (T:ℂ)^(heft b) * coeff k (bead B (-Real.log T) b j) := by
  rw [columnEntry, coeff_C_mul, Extent.token, neg_neg, Real.exp_log hT]

lemma polynomial_T (b : Q G) (j : Grade G (heft b)) (k : ℕ) :
    Rhythm (fun s => coeff k (bead B (-s) b j)) := by
  simp_rw [bead, O.Score.report]
  exact O.Enh.Uniform.flips (rhythm_v L) _ _ _ _
lemma column_rain (b : Q G) (j : Grade G (heft b)) (k : ℕ) :
    Rain 0 (fun (_ : Unit) s => coeff k (bead B (-s) b j)) := Rain.rhythm (polynomial_T L b j k)

lemma conversion_unit (η : ℝ) (d k : ℕ) :
    coeff k (conversion B η d) (leaf G d) = if k=0 then leaf G d else 0 := by
  rw [coeff_conversion]; split
  · subst k; rw [(L.paid η d).zero, Module.End.one_apply, Level.Dial_leaf]
  next hk => rw [show coeff k (B η d) (leaf G d) = 0 from ((L.paid η d).high k hk).1, map_zero]

lemma conversion_walk (η : ℝ) {d e : ℕ} (h : d ≤ e) :
    Walk h (conversion B η d) (conversion B η e) := by
  intro i p
  rw [coeff_conversion, coeff_conversion, L.continues, Level.chain]
end Column

variable {d : Fin n → ℕ} {e : Fin m → ℕ}
def budgeted (u : Scan G n) (d : Fin n → ℕ) : Prop := ∀ i, heft (u i) ≤ d i
abbrev inputs (u : Scan G n) (hu : budgeted u d) : Slots G d := fun i => cap (u i) (hu i)
lemma included (u : BasisSlots G d) : budgeted (names u) d := fun i => size_le (u i)
lemma decode_pays (v : Scan G n) (h : budgeted v d) (j : LivesP v) : budgeted (decode v j) d := h
lemma inputs_names (u : BasisSlots G d) : inputs (names u) (included u) = word u := rfl

section Score
variable (X : O.Score.Regular V)
include X
variable (hd : ∀ i, d i ≤ H) (he : ∀ i, e i ≤ H) (x : Points n) (y : Points m)
    {u : Scan G n} {v : Scan G m} (hu : budgeted u d) (hv : budgeted v e)

/-- Basis evaluation of the point array. Even off-conf (both definitions totalized by 0). -/
lemma bareEntry (k : ℕ) : bareRow V hd he x y k (inputs u hu) (inputs v hv) =
    coeff k (party (install V) x y u v) := by
  have h : Guarded (Fin.append u v) H := by
    intro i; induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact (hu i).trans (hd i)
    | right i => rw [Fin.append_right]; exact (hv i).trans (he i)
  have eqs : Fin.append (liftSlots hd (inputs u hu)) (liftSlots he (inputs v hv)) = tape _ h := by
    funext i; induction i using Fin.addCases with
    | left i => simp only [Fin.append_left, tape]; rfl
    | right i => simp only [Fin.append_right, tape]; rfl
  rw [bareRow_apply,eqs]
  by_cases Hc : forest x y ∈ conf (n+m)
  · rw [kernel_on V Hc,party,caring (Fin.append u v) h X Hc,O.Score.test, Reg.Point.story, coeff_mk]
  rw [party, install, kernel, dif_neg Hc, dif_neg Hc, map_zero]; rfl

include L
lemma measured_pulse (η : ℝ) (a : Days m) :
    bareRow V hd he x y (a none) (inputs u hu) (kSlots B η a (inputs v hv)) =
      ∑ j : LivesP v, (∏ i, coeff (a (some i)) (columnEntry B η (v i) (j i))) *
        coeff (a none) (party (install V) x y u (decode v j)) := by
  unfold kSlots
  -- first horn: literal expansion of each graded column
  have eqn (i : Fin m) : coeff (a (some i)) (conversion B η (e i)) (inputs v hv i) =
      ∑ j : Grade G (heft (v i)), coeff (a (some i)) (columnEntry B η (v i) j) •
        cap (own j) (d:=e i) (show _ from hv i) := same_grade L _ _ (hv i) _
  simp_rw [eqn, (bareRow V hd he x y (a none) (inputs u hu)).map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ((bareRow V hd he x y (a none) (inputs u hu)).map_smul_univ _
    (inputs (decode v j) (decode_pays v hv j))).trans
      (congr_arg (_ * ·) (bareEntry X hd he x y hu (decode_pays v hv j) _))

lemma measured_basis (η : ℝ) :
    measurement V B hd he x y η (inputs u hu) (inputs v hv) =
      ∑ j : LivesP v, (∏ i, columnEntry B η (v i) (j i)) *
        party (install V) x y u (decode v j) := by
  ext1 k
  rw [measurement, coeff_mk, inserted_apply, map_sum]
  simp_rw [Dframe.Constants.admits, measured_pulse L X hd he x y hu hv]
  rw [Finset.sum_comm]

lemma identifies_show (s : ℝ) :
    measurement V B hd he x (squeeze (-s) y) (-s) (inputs u hu) (inputs v hv) =
      O.Read.ShowT B (install V) s x u y v := by
  rw [measured_basis L X]
  unfold O.Read.ShowT O.Read.LensT concert
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [columnEntry]
  rw [Finset.prod_mul_distrib, ← map_prod, O.Score.priced, mul_assoc]
  rfl

-- keep exact same y, B, v and same H (center response is a different arity)
omit hd x hu in
lemma identifies_long {h : ℕ} (hh : h ≤ H) (q : Toon G h) (s : ℝ) :
    center V B he (squeeze (-s) y) hh (-s) (theory q) (inputs v hv) =
      O.Read.LongT B (install V) s (flash q) y v := by
  exact identifies_show L X (d := fun (_ : Fin 1) => h) (fun _ => hh) he (0 : Points 1) y
    (u := Single (flash q)) (fun _ => size_le q) hv s
end Score

/-- Exact product-T^W on a homogeneous Far word. (Not T raised to the sum of their caps!) -/
lemma product_account (η : ℝ) (v : Scan G m) (j : LivesP v) :
    (∏ i, columnEntry B η (v i) (j i)) =
      O.Score.Acres η (totalG v) * play (seats (B η)) v (decode v j) := by
  simp_rw [columnEntry]
  rw [Finset.prod_mul_distrib, ←map_prod, O.Score.priced]
  rfl

lemma product_T (v : Scan G m) (j : LivesP v) {T : ℝ} (hT : 0 < T) :
    (∏ i, columnEntry B (-Real.log T) (v i) (j i)) =
      PowerSeries.C ((T:ℂ)^(totalG v)) * play (seats (B (-Real.log T))) v (decode v j) := by
  rw [product_account _, O.Score.Acres, ← O.Score.season, Extent.token, neg_neg, Real.exp_log hT]

end YM.FVA2.GradedFar259
