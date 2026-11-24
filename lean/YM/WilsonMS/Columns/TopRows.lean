import YM.WilsonMS.Columns.LoopData
import YM.WilsonMS.Columns.WheelsH
/-!
# Highest unnormalized field rank at auxiliary trajectories
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.StrictMint
open MS Function Filter Set Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
  _root_.YM.MS.Shine
open Hem Mell Logarithm Pearl Train Signal Book Convolve Garment.Wave Garment.Wick Dock LoopRank
open scoped Topology ContDiff Interval
variable {G : Gauge} {h k i m r n j : ℕ} {V W X : Mob G} {F J P : Flats G} {p t : Coat G} {b : Bool}
  {q d : ℤ}

private def lims (r k : ℕ) (V : Mob G) : Prop :=
  ∀ (j : ℕ) (v : Legs (Shore G j)),
    v.length = r → ∃ x : ℂ, Tendsto (fun s : ℝ => plow (-(k : ℂ)) s V j v) atBot (𝓝 x)

private lemma fore (hp : Holds k r p F) (h : Count p k) (i : ℕ) : ∀ᶠ x in dotty, lims r k (F i x) := by
  refine (hp i).mono fun x hx => ?_
  by_cases hi : i = 0
  swap
  · have ht := Finsupp.single_eq_of_ne (b := p) hi
    simp only [Finsupp.sub_apply, ht, sub_zero] at hx
    exact fun j v he => ⟨0, hx j v he⟩
  subst i
  have he (s) : plow (-(k : ℂ)) s (F 0 x) = plow (-(k : ℂ)) s (F 0 x - p x) + p x := by
    rw [← cert, ← cert, map_sub, cert, cert, h x]
    simp
  intro j v ht
  refine ⟨p x j v, ?_⟩
  have hm := hx j v ht
  have hb : (((F - Finsupp.single 0 p) : Flats G) 0 x) = F 0 x - p x := by simp
  rw [hb] at hm
  simp_rw [he]
  simpa only [zero_add] using! hm.add_const (p x j v)

private lemma allowable {F : Mob G} (h : F ∈ pouch G r) (s : ℝ) (k : ℂ) {v : Legs (Shore G i)}
    (he : v.length > r) : plow k s F i v = 0 := by
  unfold plow
  rw [asks.mp h i (sr s v)
      (fun hv => he.not_ge (by simpa only [sr, List.length_map] using hv.smaller)),
    mul_zero]

private lemma wind_scatter {A : Type*} {T : ℝ → Shared A ℂ} (p : Sector A) (l : List A)
    (h : ∀ u v, Split u v l → Tendsto (fun t => T t u v) atBot (𝓝 0)) :
    Tendsto (fun t => scatter p l (T t)) atBot (𝓝 0) := by
  induction l generalizing T with
  | nil => exact h _ _ .nil
  | cons i l ih =>
    simp only [scatter_cons]
    refine ih (T := fun t u v => T t (i :: u) v + cross _ _ * T t u (i :: v)) ?_
    intro u v he
    simpa only [mul_zero, add_zero] using!
      (h _ _ he.left).add ((h _ _ he.right).const_mul (cross (p i) (degree p u) : ℂ))

private lemma wind_v (hT : i + j = r + 2) (hp : V ∈ pouch G i) (hw : W ∈ pouch G j) (ht : lims i 4 V)
    (hv : lims j k W) : EmptyH r k (arbor (A0 G 0) V W) := by
  let A := A0 G 0
  let U t := pulse 4 t A
  let g (t : ℝ) := plow (-(4 : ℂ)) t V
  let z (t : ℝ) := plow (-(k : ℂ)) t W
  have hm : limp U 0 := by
    unfold U A
    simp_rw [pA]
    exact limitA G
  intro m l hy
  have hq (t : ℝ) : plow (-(k : ℂ)) t (arbor A V W) = arbor (U t) (g t) (z t) := by
    unfold U g z
    rw [air_tree 4 (-(4 : ℂ)) (-(k : ℂ)) t (reverse_a G 0)]
    simp [A]
  change Tendsto (fun t => plow _ t (arbor A V W) m l) _ _
  simp_rw [hq]
  apply
    wind_scatter (T := fun t => attaches Landau.parity (U t m) (g t m) (z t m)) (field Landau.parity)
      l
  intro u v hx
  have he := split_length hx
  by_cases hc : u.length + 1 = i
  · have hs : v.length + 1 = j := (by omega)
    unfold attaches
    dsimp only
    rw [show (0 : ℂ) = ∑ _a : Cfield G m, ∑ _b : Cfield G m, ((0 : ℂ) + 0) from (by simp)]
    apply tendsto_finsetSum
    intro a ha
    apply tendsto_finsetSum
    intro b hb
    have hd (d e c q' : Cfield G m) (X : SectorP m) (w : ℂ) :
      Tendsto (fun t => U t m d e X * ((w * g t m ((c, -net u) :: u)) * z t m ((q', -(-net u)) :: v)))
        atBot (𝓝 0) := by
      obtain ⟨B, hB⟩ := ht m ((c, -net u) :: u) hc
      obtain ⟨P, hP⟩ := hv m ((q', -(-net u)) :: v) hs
      convert (hm m d e X).mul (((hB.const_mul _).mul hP)) using 1
      rfl
      simp
    exact Tendsto.add (hd a b a b _ _) (hd a b b a _ _)
  have hh : u.length + 1 > i ∨ v.length + 1 > j := by omega
  unfold attaches
  dsimp only
  rcases hh with hL | hL
  · rw [show (fun t => _) = (fun _ : ℝ => (0 : ℂ)) from ?_]
    exact tendsto_const_nhds
    funext t
    simp [show ∀ a : Shore G m, g t m (a :: u) = 0 from fun a => allowable hp _ _ (v := a :: u) hL]
  rw [show (fun t => _) = (fun _ : ℝ => (0 : ℂ)) from ?_]
  exact tendsto_const_nhds
  funext t
  simp [show ∀ a : Shore G m, z t m (a :: v) = 0 from fun a => allowable hw _ _ (v := a :: v) hL]

lemma watch_drive (h : i + j = r + 2) (hv : Carry i F) (ht : Carry j J) (hp : Holds 4 i p F)
    (hw : Count p 4) (hT : Holds k j t J) (hq : Count t k) : Watch k r (drive0 G F J) := by
  refine (vault k r).explo _ F J (fun a b => ?_)
  filter_upwards [hv a, ht b, fore hp hw a, fore hT hq b] with z hA hB hC hD
  exact wind_v h hA hB hC hD

open Emit Outlook Halo Mach Motif
variable {B : Local.Physical.Deck G} {A : Land.Booked B} (Y : Land.MS_Data G A)

lemma fee_badge (ht : Badge b (fun _ : ℂ => V) h q) : kPrice V := by
  obtain ⟨s, hS⟩ := ht.stock
  obtain ⟨u, hU⟩ := (hS.fine.tune.mer.price).exists
  exact hU

lemma bulk_rows (i : ℕ) : Holds 4 (i + 2) (gloss (pulseX G) i) (Y.bulk i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    let R (j) := invest G j
    let s := shortB i
    let P (j : ℕ × ℕ) := drive0 G (Y.bulk j.1) (Y.bulk j.2)
    let Z := ∑ j ∈ s, P j
    have he (j) (hx : j ∈ s) : j.1 < i ∧ j.2 < i ∧ (j.1 + 2) + (j.2 + 2) = (i + 2) + 2 := by
      obtain ⟨hv, hx⟩ := Finset.mem_filter.mp hx
      exact
        ⟨hx.1, hx.2, by
          obtain ht := Finset.mem_antidiagonal.mp hv
          omega⟩
    have hZ : Carry (i + 2) Z :=
      (washed _).sum _
        (fun i hi => LoopRank.heat (action_fill Y i.1) (action_fill Y i.2) (he i hi).2.2)
    have hp : Watch 4 (i + 2) Z :=
      (vault 4 (i + 2)).sum _
        (fun j hj =>
          watch_drive (he j hj).2.2 (action_fill Y _) (action_fill Y _) (ih _ (he j hj).1)
            (invest G _ |>.born) (ih _ (he j hj).2.1) (invest G _ |>.born))
    apply
      installs _ (Y.bulkOK i) (Live.stays (fee_badge (V := pulseX G i) (invest G i))) (invest G i) ?_
        (pb_coal (fun i _ => gang (Y.bulkOK i))) ?_ (watch_scale hp ((2 : ℂ)⁻¹))
    · exact
        Eventually.of_forall fun _ =>
          asks.mpr fun m =>
            LoopRank.full
              (by
                push_cast
                exact R_action G i m)
    exact fun j => ((hZ j)).mono fun z hz => (pouch G (i + 2)).smul_mem _ hz

lemma mark_rows (P : Land.Plaid B h) (j : ℕ) :
    Holds h (j + (Land.read P).grade) (fun _ : ℂ => (A.optics h P j)) (Y.marks h P j) := by
  let Z := Y.marks h P
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hv (i) := (A.law h P).grows i
    refine
      installs _ ((Y.markOK h P) j) (Live.stays (fee_badge (hv j))) (hv j) ?_
        (pm_coal (fun i _ => gang ((Y.markOK h P) i)) (fun i => gang (Y.bulkOK i)))
        ((washed _).sum _ ?_) ((vault _ _).sum _ ?_)
    · exact
        Eventually.of_forall fun i =>
          asks.mpr fun n =>
            LoopRank.full
              (by
                push_cast
                exact R_Marks (A.law h P) j n)
    · intro s hs
      obtain ⟨hh, hp⟩ := Finset.mem_filter.mp hs
      refine LoopRank.heat (action_fill Y s.1) (mark_fill Y P s.2) ?_
      obtain ht := mem_antidiagonal.mp hh
      omega
    intro t ht
    obtain ⟨hh, hp⟩ := Finset.mem_filter.mp ht
    apply
      watch_drive _ (action_fill Y t.1) (mark_fill Y P t.2) (bulk_rows Y _) (invest G _ |>.born)
        (ih t.2 hp) (hv _ |>.born)
    obtain ht := mem_antidiagonal.mp hh
    omega

lemma scanned (w : Land.Plaid B h) (n : ℕ) (s y : ℝ) :
    emptyT (n + (Land.read w).grade) h (hereZ h (Y.marks h w n) s y - A.optics h w n) := by
  let K := Y.marks h w n
  let V := A.optics h w n
  let P := K - Finsupp.single 0 (fun _ : ℂ => V)
  have ht : Badge false (fun _ : ℂ => V) h 0 := (A.law h w).grows n
  have hh : Lift (Parade P h y s) (hereZ h K s y - V) := by
    rw [show P = K - _ from rfl, page_sub, pureP (fun _ : ℂ => V) ht.born]
    exact Lift.sub (Outlook.live0 (gang (Y.markOK h w n)).dost) (Lift.stays (fee_badge ht))
  exact firstT (Lift.price hh) (observes (n := 0) hh (parade_rank (mark_rows Y w n) s y h))

lemma beginning (w : Land.Plaid B h) (n : ℕ) (s y : ℝ) (l : Legs (Shore G 0)) (j : ℕ)
    (hL : l.length = n + (Land.read w).grade) (hp : mass l + j ≤ h) :
    torch j (Archive h (Y.marks h w) n (y, s)) l = torch j (A.optics h w n 0) l := by
  let i := (mass l + j).toNat
  have hx : 0 ≤ mass l := dm l
  have he : mass l + j = i := by
    unfold i
    omega
  have hQ := scanned Y w n s y i (show i ≤ h from by omega) 0 l hL
  rw [t_minus (Lift.price (Outlook.live0 (gang (Y.markOK h w n)).dost))
      (fee_badge (V := A.optics h w n) ((A.law h w).grows n)),
    Pi.sub_apply, Pi.sub_apply, t_bud _ he, t_bud _ he] at hQ
  exact sub_eq_zero.mp hQ
end YM.WilsonMS.StrictMint
