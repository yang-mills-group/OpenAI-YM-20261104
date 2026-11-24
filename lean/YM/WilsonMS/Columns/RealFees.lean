import YM.WilsonMS.Stencil.NonlinearFit
import YM.WilsonMS.Columns.TopRows
import YM.WilsonMS.Columns.HeatTangent
/-!
# Setting the Laurent power before coupling rescaling

In field changes keep track of the *classical* top-order constraints:
keep strictly positive coupling-square powers where applicable. Still
compare to the **same** MS answers with these constraints.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.RealFees
open MS Function Filter Finset Set MeasureTheory Metric
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Real Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Cylinder Lab Draft Wind Wind.Leading Menus Lifting
  LoopRank
open StrictRank Local.Physical Land BMenu High Outlook
open Arts Rock Mach Pearl Hem Hem.Mell Dock Halo
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {q v : ℤ} {p : Team} {F : Actor G} {u V w : List (Lane4 G)} {h d i j k : ℕ}
local notation "B" => Ensure.deck G

structure Surcharge (r k : ℕ) (T : Tact (Ensure.deck G) d) : Prop extends Controlled (r + k) T where
  extra (i : Glyph B d) : r ≠ 0 → T.register i ≠ 0 → i.grade < r + k
  change (x : ℝ) : Limit (T.proof.input x).val ((↑(r + k) : ℤ) - 1)

variable (W : BasisMenu G) (x : ℝ)

lemma highestBorn (p : Team) (i : ℕ) (X : T (Dot G Cover)) (l : List (LightMode G Cover))
    (hp : ∀ t, Limit (X t).val (↑(t+d) : ℤ)) (he : l.length=i+d) :
    (wobble G p x X i).val l=(X i).val l := by
  let U := fieldV (G := G) p x ∘ Prod.fst (β := Cover)
  let Y := Program.shift p x
  have ht (j : ℕ) (n : ℕ) (hn : j < n) (l : List (LightMode G Cover)) (he : l.length = n + d) :
    (substitute Y X j).val l = 0 := by
    rw [rules, sum_stack, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [smul_stack, Pi.smul_apply,
      hp i l
          (by
            obtain hv := mem_Iic.mp hi
            omega),
      smul_zero]
  have hv : (wobble G p x X i).val l = (X i).val l := by
    change (car U (substitute Y X) i).val l = _
    rw [rolls, sum_stack, Finset.sum_apply, Finset.sum_eq_single (0, i)]
    · rw [show train U _ _ = substitute Y X i from frame_clock x p _, rules, sum_stack,
        Finset.sum_apply, Finset.sum_eq_single i]
      · unfold Y
        rw [root_first (share p x) (ann p x), one_smul]
      · intro j hj hh
        rw [smul_stack, Pi.smul_apply,
          hp j l
            (by
              obtain hz := mem_Iic.mp hj
              omega),
          smul_zero]
      simp
    · intro j hj hh
      obtain H := Finset.mem_antidiagonal.mp hj
      rw [train_v, offer,
        ht j.2 i
          (by
            by_contra! hc
            exact
              hh
                (Prod.ext
                  (by
                    dsimp
                    omega)
                  (by
                    dsimp
                    omega)))
          l he,
        mul_zero]
    simp
  exact hv

lemma unaltered (W : XSpace.Initialize G) (x : ℝ) (p : Team) (J : Glyph B d) (i : ℕ)
    (l : List (LightMode G Cover))
    (he : l.length = i + J.grade) :
    (preambleW W p J x i).val l = (Webs.symbol (W.surveys J.size) (data0 J).val).val l := by
  let X := vertices W J
  have hp (t : ℕ) : Limit (X t).val (↑(t + J.grade) : ℤ) := fun w hw =>
    piecesP W J t w fun h =>
      (by
        obtain ht := h.smaller
        omega)
  have hv := highestBorn x p i X l hp he
  rw [show (preambleW W p J x i).val l = _ from hv]
  unfold X vertices
  rw [Pi.add_apply, add_stack, Pi.add_apply, Finset.sum_apply, sum_stack, Finset.sum_apply,
    Finset.sum_eq_zero, add_zero]
  · change Book.mask _ _ l = _
    rw [enough l (by omega)]
    rfl
  intro j hj
  exact
    strange l
      (by
        have hp := j.2.isLt
        omega)

variable {J : Glyph (Ensure.deck G) d} {P : Acts (Ensure.deck G) d}

lemma present (h : ∀ i, Surcharge i J.grade (P i)) (hp : FitOrder J (P 0)) (k : ℕ)
    (l : List (LightMode G Cover)) (he : l.length = k + J.grade) (p : Team) :
    (scoreW W p P x k).val l = (W.pre p J x k).val l := by
  have hm : Limit (Menus.motto p P x k).val ((↑(k + J.grade) : ℤ) - 1) := by
    rw [sky]
    refine Limit.add (Limit.up (lapLimit ((h k).change x)) (by omega)) ?_
    rw [sum_stack]
    exact
      Limit.sum _
        (fun j hj =>
          (rootLimit (style_limit p x G j.1) ((h j.2).change x)).up
            (by
              obtain ht := Finset.mem_antidiagonal.mp hj
              omega))
  rw [scoreW, Pi.add_apply, add_stack, Pi.add_apply, hm l (by omega), add_zero]
  unfold rentW
  rw [sum_stack, Finset.sum_apply]
  rw [Finset.sum_eq_single J]
  · rw [sum_stack, Finset.sum_apply, Finset.sum_eq_single (0, k)]
    · rw [oil, hp.Single _ le_rfl, if_pos rfl, Polynomial.eval_one, Complex.ofReal_one]
      dsimp only
      rw [one_smul]
    · intro j hj ht
      have hs := mem_antidiagonal.mp hj
      have hb : j.1 ≠ 0 := fun hv =>
        ht
          (Prod.ext hv
            (by
              dsimp
              omega))
      by_cases H : (P j.1).register J = 0
      · rw [oil, H, Polynomial.eval_zero, Complex.ofReal_zero, zero_smul]
        rfl
      rw [smul_stack, Pi.smul_apply,
        W.pre_leg p J _ x l
          (by
            obtain he := (h j.1).extra J hb H
            omega),
        smul_zero]
    simp
  · intro b hb hh
    rw [sum_stack, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    have he' := mem_antidiagonal.mp hj
    by_cases hv : (P j.1).register b = 0
    · rw [oil, hv, Polynomial.eval_zero, Complex.ofReal_zero, zero_smul]
      rfl
    have hx : b.grade < j.1 + J.grade := by
      by_cases he : j.1 = 0
      swap
      exact (h j.1).extra b he hv
      rw [he, zero_add]
      by_contra! H
      rw [he, hp.Single _ H, if_neg hh] at hv
      contradiction
    rw [smul_stack, Pi.smul_apply, W.pre_leg p b _ x l (by omega), smul_zero]
  simp
local notation "X" => JRad.book G

lemma readX (U : Land.Plaid (B) d) (n : ℕ) :
    ((JRad.book G).optics d U) n 0 =
      Book.mask (↑(n + (Land.read U).grade) : ℤ)
        (JRad.optic G (Theater.ΕData (Ensure.deck G) (Land.read U)) 1 0) := by
  let Q := (X).optics d U
  let R := Land.read U
  have hp (i : ℕ) : Book.rank (↑(i + R.grade) : ℤ) (Q i 0) := by
    push_cast
    exact R_Marks ((X).law d U) i 0
  rw [← JRad.Book_formula]
  funext l
  by_cases hx : (l.length : ℤ) = (↑(n + (Land.read U).grade) : ℤ)
  swap
  · rw [show ((JRad.book G).optics d U) n 0 l = 0 from hp n l ?_, strange l hx]
    rw [mod_int]
    exact hx
  rw [enough l hx]
  let L := Motif.Literal.value (Mob G) 1
  change (Q n 0 l) = L Q 0 l
  rw [← Finsupp.sum_single Q]
  unfold Finsupp.sum
  rw [map_sum, Finset.sum_apply', Finset.sum_apply, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold L
  rw [Motif.Literal.value_sl, one_pow, one_smul]
  by_cases hv : n = i
  · subst n
    rw [Finsupp.single_eq_same]
  rw [Finsupp.single_eq_of_ne hv, hp i l ?_]
  rfl
  rw [mod_int]
  unfold R
  omega

structure FirstFit (W : BasisMenu G) : Prop where
  sort {d : ℕ} (p : Team) (x : ℝ) (v : Land.Plaid (Ensure.deck G) d) (n : ℕ):
    Fits (W.pre p (Land.read v) x n) ((JRad.book G).optics d v n 0)
      (n+(Land.read v).grade) d false

lemma primary_fit (W : XSpace.Initialize G) : FirstFit (↑W : BasisMenu G):= by
  constructor; intro d p x U n
  let T:= Land.read U
  rw [readX]
  unfold Fits
  let R := n + T.grade
  let V := Webs.symbol (W.surveys d) (data0 T).val
  have ht : mask (R : ℤ) (run (preambleW W p T x n))= mask R (run V):=by
    rw [← Tone.grade,← Tone.grade]; congr 1
    apply Subtype.ext
    ext1 l
    by_cases hh : (l.length : ℤ)=(R : ℤ)
    · refine (enough l hh).trans (Eq.trans (b := V.val l) ?_ (enough l hh).symm)
      exact unaltered W x p T n l (Int.ofNat_inj.mp hh)
    exact (strange l hh).trans (strange l hh).symm
  change Face wfield (mask _ (run (preambleW W p T x n))) _ _ _
  rw [ht] -- casts
  exact AllJets.classical_jet (W.surveys _) (dataHere T) _

lemma top_score (he : FirstFit W) (U : Land.Plaid (B) d) (h : ∀ i, Surcharge i (Land.read U).grade (P i))
    (hp : FitOrder (Land.read U) (P 0)) (p : Team) (n : ℕ) :
    Fits (scoreW W p P x n) ((JRad.book G).optics d U n 0) (n + (Land.read U).grade) d false := by
  let T := Land.read U
  let R := n + T.grade
  let V := W.pre p T x n
  have ht : mask (↑R : ℤ) (run (scoreW W p P x n)) = mask R (run V) := by
    rw [← Tone.grade, ← Tone.grade]
    congr 1
    apply Subtype.ext
    ext1 l
    by_cases hh : (List.length l : ℤ) = (↑R : ℤ)
    · apply Eq.trans (enough _ hh)
      refine Eq.trans (b := V.val l) ?_ (enough l hh |>.symm)
      exact
        present W x h hp n l
          (by
            change (↑l.length : ℤ) = ↑(n + (Land.read U).grade) at hh
            omega)
          p
    exact (strange l hh).trans (strange l hh).symm
  unfold Fits
  change Face wfield (mask _ _) _ _ false
  rw [show mask _ _ = mask _ _ from ht]
  exact he.sort p x U n

lemma eliminates (hq : RankBudget W) (hhf : FirstFit W) (M : Land.MS_Data G (JRad.book G)) (hG : G.Simple)
    (p : Team) (he : Valid p)
    (J : Plaid B d) (h : ∀ i, Surcharge i (Land.read J).grade (P i))
    (hp : FitOrder (Land.read J) (P 0)) (u : ℕ) {v : ℤ} (hx : v ≤ d) (x : ℝ) :
    High.slice ((seekW W p d).wake P u - Archive d (M.marks d J) u) false (u + (Land.read J).grade) v
        x =
      0 := by
  let R := M.marks d J
  let D := rowFull W p P
  let Z := Archive d R
  have hz := Outlook.fieldD M.bulkOK (M.markOK d J) Motif.wisdom (((JRad.book G).law d J).moodQ)
  apply Wind.Leading.excuse (F := col D) (H := Z) ?_ ?_ ?_ hx x
  · rintro ⟨a, t⟩ w hw j hL
    have ht i : riseH (run (BMenu.scoreW W p P a i)) (i + (Land.read J).grade) (d : ℤ) false := by
      intro l hh hc
      obtain hi := Lifting.faces (top_score _ _ hhf J h hp p i) l
      rw [show fieldVal (run _) (ray l) = _ from ?_]
      exact ⟨_, hi⟩
      exact
        funext fun v =>
          (enough (sail (ray l) v) (h := ((i + (Land.read J).grade : ℕ) : ℤ)) (by simp [hh])).symm
    let H := scoreW W p P a u
    let K := (JRad.book G).optics d J
    have h' : torch j (run H) w = torch j (K u 0) w := by
      rw [Lifting.faceAt (top_score _ _ hhf J h hp p u) hw j hL]
      let U : Mob G := K u
      have ha := ((JRad.book G).law d J).grows u
      have he : Home U d := ha.born 0
      have hk := StrictMint.fee_badge (V := U) ha
      let L : ℕ := (fieldDim wfield w + j).toNat
      have hv : fieldDim wfield w + j = L := by
        unfold L
        obtain hx := Detect.length_pay w
        omega
      have hq : Tad U L = if d = L then U else 0 := by
        rw [← show Tad U d = U from (he.complete hk).symm]
        rw [t_already d hk L]
      have hh := congr_fun (congr_fun hq 0) w
      rw [t_bud (l := w) (m := 0) U (j := j) (n := L) hv] at hh
      change torch j (K u 0) w = _ at hh
      rw [hh]
      split <;> rename_i hE
      · rw [if_pos (by omega : d = L)]
      rw [if_neg (by omega : d ≠ L)]
      rfl
    exact
      (running_w (P := D) a _ he hG (skyPC G p) (feeds W p P)
            (score_b W hq he P (Land.read J).grade (fun i => h i |>.toControlled) a) ht w hw hL).trans
        (h'.trans (StrictMint.beginning M J u _ _ w j hw hL).symm)
  · exact fun ⟨x, t⟩ w => ((feeds W p P).owes u |>.stay x).joint.routine _ _
  exact fun x w =>
    (hz.master.road ℝ (ray w) u (Nat.zero_le _) (fun v => Bool.noConfusion v)
          (fun v => Bool.noConfusion v)).1
      x
end YM.WilsonMS.RealFees
