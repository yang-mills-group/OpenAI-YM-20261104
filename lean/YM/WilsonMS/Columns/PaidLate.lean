import YM.WilsonMS.Columns.RealFees
/-! # Choices with classical coupling grading -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.PaidLate
open MS Function Filter Finset Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open LogTime Domain Local.Physical High Knobs Wind Wind.Leading Menus Land Motif Mach Lifting BMenu
  Rider Trading Bin Cylinder Lab Draft Orient
open StrictMint RealFees LoopRank LoopRank.MChoice
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {k i h d : ℕ} {b : Bool} {P : Prescription (Ensure.deck G)}
local notation "B" => Ensure.deck G

abbrev Inc (J : Glyph B d) (i : ℕ) :=
  { u : Tact B d // (i = 0 → FitOrder J u) ∧ Surcharge i J.grade u }
variable (J : Glyph (Ensure.deck G) d)

def build (i : ℕ) : Inc J i := by
  by_cases he : i = 0
  · subst i
    refine
      ⟨(primed J 0).val, (primed J 0).property.1, (primed J 0).property.2, fun _ hp _ =>
        (hp rfl).elim, fun _ _ _ => ?_⟩
    unfold primed
    simp only
    rfl
  refine
    ⟨0, (fun ht => (he ht).elim), ⟨fun _ ht => (ht rfl).elim, fun _ _ _ => rfl⟩, fun _ _ ht =>
      (ht rfl).elim, fun _ _ _ => rfl⟩

def stack (P : Code (Inc J)) : Acts B d := fun i => (P i).val

def knobs (W : BasisMenu G) (p : Team) : Knobs (Inc J) G
    where
  wake i := (seekW W p d).wake (stack J i)
  stay _ _ _ h := (seekW W p d).stay _ _ _ (fun i hi => congr_arg Subtype.val (h i hi))

lemma authorized (Y : MS_Data G (JRad.book G)) (W : BasisMenu G) (hR : RankBudget W) (hhF : FirstFit W)
    (hG : G.Simple) (p : Team)
    (he : Valid p) (hp : Fixed (col (skyline G p)) (Outlook.Archive 4 Y.bulk) true 4 1)
    (j : Plaid B d) :
    ∃ P : Acts B d,
      (∀ i, Surcharge i (Land.read j).grade (P i)) ∧
        FitOrder (Land.read j) (P 0) ∧
          Fixed (col (rowFull W p P)) (Outlook.Archive d (Y.marks d j)) false d 0 := by
  let K := knobs (Land.read j) W p
  let J := Land.read j
  let S := Outlook.Archive d (Y.marks d j)
  have ht (P : Code (Inc J)) : Spheres wave (spaceL G) (col (skyline G p)) (K.wake P) 1 0 false :=
    (mark_seekW W (p := p) (d := d) hG).law _
  have hh := Outlook.fieldD Y.bulkOK (Y.markOK d j) Motif.wisdom (((JRad.book G).law d j).moodQ)
  suffices he : ∃ X : Code (Inc J), Fixed (K.wake X) S false d 0
    by
    obtain ⟨P, hP⟩ := he
    exact ⟨stack _ P, fun i => (P i).property.2, (P 0).property.1 rfl, hP⟩
  refine
    assigned ht hh.master hh.good (fun i => (mark_seekW W (p := p) hG).occurs (stack J i)) hh.open' ?_
      (by omega) ?_ (build J)
  · intro X n hn hx i hi r
    exact
      hp (n - i)
        (by
          obtain he := path_in hi
          omega)
        _ (fun _ => Nat.succ_pos r)
  intro n hn r hFig u hu hv X EE HE
  let M := K.wake X n - S n
  let T := High.slice M false r u
  have hz := advanced (ht X) hh.master hn hFig EE
  let P := stack J X
  have hx (i) : Surcharge i J.grade (P i) := (X i).property.2
  by_cases hb : Allows (n + J.grade) r
  swap
  · refine ⟨X, Move.refl T ?_⟩
    intro i w _ hw
    rw [show T = 0 from
        Leader.rank_absent (P := K.wake X n)
          (fun i =>
            Pm_b i.1 (feeds W p P) (skyPC G p) he
              (score_b W hR he P J.grade (fun i => hx i |>.toControlled) i.1) n (exp i.2))
          (mark_archive Y j n) hb]
    rfl
  by_cases hr : r < n + J.grade
  swap
  · refine ⟨X, Move.refl T ?_⟩
    intro i w _ hw
    have he' : r = n + (Land.read j).grade := Nat.le_antisymm hb.smaller (Nat.le_of_not_gt hr)
    unfold T
    rw [he']
    exact congr_fun (eliminates W hR hhF Y hG p he j hx ((X 0).property.1 rfl) n hv i) w
  have hR := slice_ready hz hv (Ready.sub ((ht X).poly n) (hh.master.poly n))
  have hL (i : ℝ) : T i ∈ Lease G u r 0 :=
    lease_one.mpr
      ⟨slice_solid hz hv fun t => ((ht X).trueC n t).sub (hh.master.trueC n t), slice_form hz hv,
        rank_slice⟩
  have ha (i : ℝ) : natQ (T i) = 0 :=
    funext
      (fun l => closes (ht X) hh.master hh.good hn hFig EE hv HE i l (fun v => Bool.noConfusion v))
  obtain ⟨a, g, h0, h1, hJ, hI, h'⟩ := mark_inter hR hL ha B
  obtain ⟨Q, D, hQ, hT, hW, hA⟩ :=
    MChoice.additional W J P p hu hv h0 h1 hJ hI (hx n |>.toControlled) hb
  let A := Menus.patch P Q D n
  have hy : ∀ i, Surcharge i J.grade (A i) := by
    intro i
    by_cases he : i = n
    swap
    · rw [show A i = P i from patch_bef P Q D he]
      exact hx i
    subst i
    refine ⟨hA, fun l hz he => ?_, fun x => ?_⟩
    · unfold A Menus.patch at he
      rw [if_pos rfl] at he
      change (P n).register l - Q l ≠ 0 at he
      by_cases HT : Q l = 0
      rw [HT, sub_zero] at he
      exact (hx n).extra l hz he
      rwa [hQ.grade l HT]
    unfold A Menus.patch
    rw [if_pos rfl]
    exact ((hx n).change x).sub ((D.ranks x).up (by omega))
  let X' : Code (Inc J) := fun i =>
    ⟨A i,
      (fun he => by
        subst i
        exact fix_order (P := P) ((X 0).property.1 rfl) hQ hT.le (by omega)),
      hy i⟩
  have hm : ∀ i < n, (X i) = (X' i) := fun i hi => Subtype.ext (hW.past i hi)
  refine
    ⟨X',
      Move.replace
        (rewind (K := K) rfl rfl hm (fun i => (((feeds W p P).owes n).stay i).joint)
          (fun i => (((feeds W p A).owes n).stay i).joint) (recognition W hW))
        (fun i w hw hI => congr_fun (congr_fun h' i) w)⟩
section sym

lemma orient {x : Acts B d} (h : Surcharge i k (x i)) (s : Signed) : Surcharge i k (trade s x i) := by
  refine ⟨colour h.toControlled s, fun b hi hb => ?_, fun a => slimmer _ (h.change a)⟩
  by_contra ht
  rw [ledger] at hb
  apply hb
  apply Finset.sum_eq_zero
  intro a _
  by_cases hz : (x i).register a = 0
  rw [hz, smul_zero]
  rw [show lines s a b = 0 from ?_, zero_smul]
  apply Classical.byContradiction
  intro he
  apply ht
  rw [← (bins s a b he).2]
  exact h.extra a hi hz

lemma coins {I : Type} (X : Finset I) (F : I → Acts B d) (c : I → ℝ) (a : Acts B d)
    (h : Ticket a X c F) (hv : ∀ i' ∈ X, c i' ≠ 0 → Surcharge i k (F i' i)) : Surcharge i k (a i) := by
  refine
    ⟨collection X F c a h (fun i hi he => (hv i hi he).toControlled), fun z hi ht => ?_, fun y => ?_⟩
  · by_contra! he
    rw [h.reg, Finset.sum_apply] at ht
    apply ht
    exact
      Finset.sum_eq_zero fun j hj => by
        by_cases hx : c j = 0
        rw [hx, zero_smul]
        rfl
        change c j • (F j i).register z = 0
        rw [show (F j i).register z = 0 from
            Classical.byContradiction fun hm => (not_lt_of_ge he) ((hv j hj hx).extra z hi hm),
          smul_zero]
  rw [h.pf, Finset.sum_apply, sum_stack]
  exact
    Limit.sum _ fun j hj => by
      by_cases hx : c j = 0
      rw [hx, Complex.ofReal_zero, zero_smul]
      exact fun l _ => rfl
      exact Limit.smul _ ((hv j hj hx).change y)

lemma styleH {V : Plaid B d → Acts B d} (h : ∀ v, Surcharge i (Land.read v).grade (V v i))
    (v : Plaid B d) : Surcharge i (Land.read v).grade (balance V v i) := by
  refine
    coins _ _ _ _ (balanced ..)
      (fun s _ _ => coins _ _ _ _ (delivering V s v) fun k _ ht => orient ?_ _)
  rw [show (Land.read v).grade = (Land.read k).grade from congr_arg Fin.val (Bin.passes _ _ _ ht)]
  exact h k

lemma unitG (i : Plaid B 0) (n : ℕ) : Surcharge n (Land.read i).grade (bareG i n) :=
  ⟨neutral i n, (fun _ ht h => False.elim (h (if_neg (fun h => ht h.1)))), fun _ _ _ => rfl⟩
end sym

structure StrictAccount (P : Prescription B) : Prop extends TrueAccount P where
  collect d j i : Surcharge i (Land.read j).grade (P.fees d j i)

/-- One table across all orders. No coefficients ready from actual-to-formal
estimates. Built from the supplied MS cohomological matching inside with the
strengthened initialization/appearance rule on all marked vertices. -/
theorem earnings (W : BasisMenu G) (hF : Fair W) (hR : RankBudget W) (hFit : FirstFit W)
    (fE : XSpace.Initialize G) (hs : ∀ p (i : Glyph (Ensure.deck G) 0) x,W.pre p i x=preambleW fE p i x)
    (A : MS_Data G (JRad.book G)) (h : G.Simple) :
    ∃ S : Land.Prescription B, Commuting S ∧ Installed W A S ∧ StrictAccount S := by
  obtain ⟨p, hp, hT⟩ := Leader.oddWaves A h
  choose R hr hK hR using fun d (j : Plaid B d) => authorized A W hR hFit h p hp hT j
  let X (d : ℕ) (i : Plaid B d) : Acts B d :=
    match d, i with
    | 0, i => bareG i
    | d + 1, i => balance (R (d + 1)) i
  have hx (d i) : FitOrder (Land.read i) (X d i 0) := by
    cases d with
    | zero => exact Bare_init _
    | succ d => exact economy (R _) _ (hK _)
  have ha (d i k) : Surcharge k (Land.read i).grade (X d i k) := by
    cases d with
    | zero => exact unitG ..
    | succ d => exact styleH (fun i => hr _ i k) i
  refine ⟨⟨p, X, hx⟩, ⟨?_, fun _ => rfl⟩, ⟨hT, ?_⟩, ⟨hp, fun d j i => (ha d j i).toControlled⟩, ha⟩
  · intro d
    cases d with
    | zero => exact Bare_same
    | succ d => exact same _
  intro d i
  cases d with
  | zero =>
    have hm (q : Acts B 0) : scoreW W p q=scoreW fE p q := by
      ext1 x; unfold scoreW; congr 1; funext k; unfold rentW
      simp_rw [hs]
    have he : rowFull W p (bareG i)=rowFull fE p (bareG i):= by
      funext n
      refine mark_birth (feeds W p (bareG i)) (feeds _ p _) (k:=n+1) (fun j _ x=>?_) n (by omega)
      rw [hm (bareG i)]
    change Fixed (col (rowFull W p (bareG i))) _ _ _ _
    rw [he]; exact Rider.fixed i fE p A h hT
  | succ d => exact Rider.purse W A p _ i hF (hR _)

theorem earned (W : XSpace.Initialize G) (A : MS_Data G (JRad.book G)) (h : G.Simple) :
    ∃ S : Land.Prescription B, Commuting S ∧ Installed W A S ∧ StrictAccount S :=
  earnings (G:=G) W (actsPre W) (primaryRank W) (RealFees.primary_fit W) W (fun _ _ _=> rfl) A h
end YM.WilsonMS.PaidLate
