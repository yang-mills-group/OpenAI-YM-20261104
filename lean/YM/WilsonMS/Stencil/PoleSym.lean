import YM.WilsonMS.Stencil.BOcean
/-!
# Pole-equivariance, in the *actual* minimal subtraction program

Rotation, linear recombinations. Pacts are germs near dimensional specialization;
do not infer equality away from that domain. These will imply rotation after specialization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.HBeam
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment
  Color _root_.YM.MS.Shine Outlook
open Hem Mell Logarithm Pearl Train Dock Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {m n ℓ d : ℕ} (s : Signed) {J V : Mob G} {i : ℂ} {q r : ℤ}
local notation "X" => rotateMob s G

lemma rotation (V : Mob G) (l : Legs (Shore G n)) :
    rotateMob s G V n l = signs s l * V n (List.map (mov s) l) :=
  phase ..

lemma rotate_sym (hv : Rock.sym V) : Rock.sym (X V) := by
  intro n l i j r
  simp only [rotation, List.map_append, List.map_cons]
  rw [hv n _ _ _ _]
  have he (u : Shore G n) : field Landau.parity (mov s u) = field Landau.parity u := by
    rcases u with ⟨⟨⟨_ | a, _ | _⟩, v⟩, p⟩ <;> rfl
  simp_rw [signs, List.map_append, List.prod_append, List.map_cons, List.prod_cons, he]
  ring

lemma rotate_Color (hv : ShadeG V) : ShadeG (X V) := by
  intro n g
  have ht (w : Rack G n) (l : Legs (Shore G n)) :
    repeatC g (shiftR s G n w) l = signs s l * repeatC g w (List.map (mov s) l) := by
    induction l generalizing w with
    | nil => simp [shiftR, signs]
    | cons i l ih =>
      let T := shiftR s G n
      let L := setLeg i
      let u := mov s i
      rw [repeat_cons, List.map_cons, repeat_cons]
      simp only [signs, List.map_cons, List.prod_cons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      let c : ℂ := digit s i.1
      let f := Koszul.D (setLeg u j) w
      have hm : Koszul.D (L j) (T w) = c • T f := by
        funext v
        change T w (_ :: _) = c * T f v
        simp only [T, phase, signs, List.map_cons, List.prod_cons, mul_assoc]
        rfl
      rw [hm, map_smul, (Pi.smul_apply ..), show repeatC g (T f) l = _ from ih f]
      change _ * (c * _) = (c * _) * (wc g i.1.2 j * _)
      ring
  exact
    funext fun l =>
      (ht (V n) l).trans
        (by
          rw [hv]
          exact (phase ..).symm)

lemma rotate_collar (H : Collar q V) : Collar q (X V) := by
  refine ⟨rotate_sym s H.sym, rotate_Color s H.color, ?_⟩
  intro n l hl
  rw [rotation, H.ghost, mul_zero]
  convert hl using 1
  clear hl
  induction l with
  | nil => rfl
  | cons i l ih =>
    rcases i with ⟨⟨⟨_ | a, _ | _⟩, v⟩, p⟩ <;> simp only [chargeInt, List.map_map] at * <;>
        rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons] <;>
      rfl

lemma rotate_sight (H : Sight V) : Sight (X V) := by
  intro n l
  rw [rotation, rotation, star_mul, ← H]
  rw [show star (signs s l) = signs s l from ?_, show signs s (invertMom l) = signs s l from ?_]
  · rw [mul_comm]
    congr 2
    induction l with
    | nil => rfl
    | cons i l ih =>
      rcases i with ⟨a, p⟩
      unfold invertMom at *
      simp only [List.map_cons, ih]
      change (_, (grip s).turn (-p)) :: _ = _
      rw [map_neg]
  · simp only [signs, invertMom, List.map_map]
    rfl
  induction l with
  | nil => simp [signs]
  | cons i l ih =>
    rw [show signs s (i :: l) = (digit s i.1 : ℂ) * signs s l from rfl, star_mul, ih]
    simp [mul_comm]

lemma rotate_trail (h : Mell.Trail J V i) : Mell.Trail (X J) (X V) i := by
  constructor
  intro t
  simp_rw [← rotate_plow]
  intro n l
  simp_rw [rotation]
  exact (h.derive t n _).const_mul _

section flat
variable {T U : Flats G} {f g : Coat G}

abbrev moveK (s : Signed) (G : Gauge) :=
  tapeL (fun _ : ℂ => rotateMob s G)

def moveM (s : Signed) (G : Gauge) :=
  blast 0 (moveK s G)
local notation "L" => moveM s G
local notation "Y" => moveK s G

lemma moveK_at (f : Coat G) (p : ℂ) : Y f p = X (f p) :=
  rfl

lemma moveM_at (n : ℕ) (T : Flats G) : L T n = Y (T n) :=
  blade 0 ..

lemma rotate_mer (h : mer f) : mer (Y f) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n, Live.congr (rotate_live s h) ?_⟩
  exact .of_forall fun i => map_smul X (i ^ n) (f i)

lemma rotate_cap (h : Cap0 false q r f) : Cap0 false q r (Y f) := by
  obtain ⟨⟨⟨H, ht⟩, hp, hv⟩, hc⟩ := h
  refine
    ⟨⟨⟨rotate_mer s H, ht.mono fun _ hi => carries s hi⟩, hp.mono fun _ he => rotate_collar s he, ?_⟩,
      ?_⟩
  · apply Eventually.mono hv
    intro i hi
    exact rotate_sight s hi
  apply hc.mono
  intro i hi
  replace hi : Issue r _ := hi
  intro n v hv
  rw [moveK_at, rotation, hi, mul_zero]
  simpa using hv

lemma rotate_clock (h : ClockD false q r T) : ClockD false q r (L T) := fun i => by
  rw [moveM_at]
  exact rotate_cap s (h i)

lemma rotate_cool (h : Cool f) : Cool (Y f) := by
  obtain ⟨n, W, hW⟩ := polar h
  rw [hW, map_sum]
  exact
    (cone G).sum_mem
      (fun i _ =>
        show (Y (Ice (i + 1) (W i))) ∈ _ from
          (show Y (Ice (i + 1) (W i)) = Ice (i + 1) (X (W i)) from
              funext (fun k => map_smul X (k⁻¹ ^ (i + 1)) (W i))) ▸
            (iceC _ _ (by omega)))

lemma rotate_parade (T : Flats G) (n : ℕ) (x y : ℝ) : Y (Parade T n x y) = Parade (L T) n x y := by
  rw [Page (T.support ∪ (L T).support) Finset.subset_union_left,
    Page (T.support ∪ (L T).support) Finset.subset_union_right, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  funext z
  rw [moveM_at]
  change X (hikeP _ _ _ _ _ _) = hikeP _ _ _ _ _ (X (T i z))
  unfold hikeP
  rw [map_smul, rotate_plow]

lemma rotate_stay (hp : Stay n T) : Stay n (L T) := fun x y => by
  rw [← rotate_parade]
  exact rotate_live s (hp x y)

lemma rotate_joint (hp : Joint n T U f g) : Joint n (L T) (L U) (Y f) (Y g) := by
  constructor
  · filter_upwards [hp.advance] with i hi ℓ
    rw [moveM_at, moveM_at]
    exact rotate_trail s (hi ℓ)
  · exact rotate_stay s hp.toll
  · intro i
    rw [moveM_at]
    exact rotate_mer s (hp.wet i)
  · exact rotate_cool s hp.ice
  · exact rotate_mer s hp.worth
  · intro i t
    rw [moveK_at, ← rotate_plow, hp.back i t]
  unfold Return
  rw [← map_add]
  filter_upwards [hp.sip] with i hi n w
  rw [moveM_at, moveK_at]
  simp_rw [moveK_at, ← rotate_plow, rotation]
  exact (hi n _).const_mul _

lemma spin_cycle (ht : Moony false T) : Pact (L (step0 G T)) (step0 G (L T)) := by
  let K := A0 G 0
  intro i
  rw [moveM_at]
  rcases i with _ | i
  · simp only [step0, CycleN, bland zero_lt_one, map_zero]
    exact EventuallyEq.rfl
  simp_rw [step0, CycleN, blade, moveM_at]
  filter_upwards [sunny (ht i), high0] with z hz hX
  change X (swamp K (T i) z) = swamp K (Y (T i)) z
  rw [swamp_spec (c_bo ..) hz hX, swamp_spec (c_bo ..) (rotate_form s hz) hX, map_smul,
    rotate_ocean s hz (c_bo ..) hX]
  rfl

lemma rotate_tree (T U : Flats G) : L (drive0 G T U) = drive0 G (L T) (L U) := by
  let S := L
  let P := drive0 G
  induction T using Finsupp.induction_linear with
  | zero => simp
  | add T V hT hV => simp only [map_add, LinearMap.add_apply, hT, hV]
  | single i f =>
    induction U using Finsupp.induction_linear with
    | zero => simp
    | add T V hT hV => simp only [map_add, hT, hV]
    | single j g =>
      let K := A0 G 0
      let M := tapeB (squad K)
      have ht (a b : Coat G) : P (.single i a) (.single j b) = Finsupp.single (j + i) (M a b) := by
        change explode M _ _ = _
        rw [explodeL, Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp
      change S (P _ _) = P (S (.single i f)) (S (.single j g))
      rw [ht]
      unfold S moveM
      simp only [blast_sl, add_zero]
      rw [ht]
      congr 1
      exact funext fun z => rotate_arbor s (f z) (g z) (A_caps G 0) (cl_a G 0)

lemma rotate_cost (hb : Gang true n q T) : Pact (L T) T := by
  obtain ⟨r, hp⟩ := hb.price
  intro m
  rw [moveM_at]
  filter_upwards [(show ∀ᶠ i in dotty, Sturdy true (T m i) from (hp m).fine.tune.dice)] with z hz
  exact funext fun t => hz.turn t _ (fun i => Bool.noConfusion i)
end flat
section marked
variable {F H S : T (Flats G)} {U V : Flats G} {a p q b t v u : T (Coat G)} {ℓ : ℤ}
local notation "L" => moveM s G
local notation "Y" => moveK s G

lemma rotate_platform (h : leader G F b u) (n : ℕ) (H : T (Flats G)) :
    Pact (L (platform F n H)) (platform F n (L ∘ H)) := by
  unfold platform
  rw [map_sum]
  simp_rw [rotate_tree]
  exact pact_sum _ (fun i _ => pair_pact _ (rotate_cost s (gang (h i.1))) (fun _ => EventuallyEq.rfl))

lemma rotate_comet (hB : leader G F b u) (hx : comet n ℓ F a H p) :
    comet n ℓ F (Y ∘ a) (L ∘ H) (Y ∘ p) := by
  intro m
  obtain ⟨⟨r, hT, hX, h⟩, hq⟩ := hx m
  obtain he := rotate_joint s hT
  rw [map_add] at he
  refine
    ⟨⟨r, he.via (common (rotate_platform s hB m H) (spin_cycle s (clockMoon hX))), rotate_clock s hX,
        rotate_cap s h⟩,
      fun i => i.elim⟩

lemma plat_plus (n : ℕ) (U Z : T (Flats G)) :
    platform F n (U + Z) = platform F n U + platform F n Z := by
  simp only [platform, Pi.add_apply, map_add, Finset.sum_add_distrib]

lemma plus_comet (h : comet n ℓ F a S p) (he : comet n ℓ F q H b) :
    comet n ℓ F (a + q) (S + H) (p + b) := by
  intro m
  obtain ⟨⟨k, hT, hX, hW⟩, hp⟩ := h m
  obtain ⟨⟨r, hK, hH, hA⟩, hv⟩ := he m
  refine
    ⟨⟨max k r, ?_, Cap0.heap.plus (clockTrans hX (le_max_left ..)) (clockTrans hH (le_max_right ..)),
        (hW.collects (le_max_left ..)).add (hA.collects (le_max_right ..))⟩,
      fun i => i.elim⟩
  rw [Pi.add_apply, plat_plus, map_add, add_add_add_comm]
  exact hT.plus hK

lemma smul_comet (h : comet n ℓ F a H b) (c : ℂ) (hc : star c = c) :
    comet n ℓ F (c • a) (c • H) (c • b) := by
  intro i
  obtain ⟨⟨r, hT, hX, hV⟩, hp⟩ := h i
  refine ⟨⟨r, ?_, fun i => (hX i).smul hc, hV.smul hc⟩, fun i => i.elim⟩
  simp only [platform, Pi.smul_apply, map_smul, ← Finset.smul_sum, ← smul_add]
  exact hT.scale c

lemma zero_comet : comet n ℓ F 0 0 0 := by
  intro i
  unfold PathD
  rw [show platform F i 0 = 0 from by simp [platform]]
  exact zero_sing False

lemma sum_comet (P : Finset I) (A : I → T (Coat G)) (Z : I → T (Flats G)) (B : I → T (Coat G))
    (h : ∀ i ∈ P, comet n ℓ F (A i) (Z i) (B i)) :
    comet n ℓ F (∑ i ∈ P, A i) (∑ i ∈ P, Z i) (∑ i ∈ P, B i) := by
  classical
    induction P using Finset.induction with
  | empty => simpa using zero_comet (F := F) (n := n) (ℓ := ℓ)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact plus_comet (h i (by simp)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma four_rot (hv : Stay n U) (z : Clock ℝ) :
    shiftR s G 0 (Outlook.four n U z) = Outlook.four n (L U) z := by
  obtain ⟨x, y⟩ := z
  let Q := hereZ n U y x
  refine congr_fun (Lift.unique (F := rotateMob s G Q) ?_ (live0 (rotate_stay s hv))) 0
  rw [← rotate_parade]
  exact rotate_lift s (live0 hv)

lemma four_pact (h : Stay n V) (hx : Stay n U) (he : Pact V U) (z : Clock ℝ) :
    Outlook.four n V z = Outlook.four n U z := by
  obtain ⟨x, y⟩ := z
  refine congr_fun (Lift.unique (Lift.congr (live0 h) ?_) (live0 hx (s := y) (y := x))) 0
  exact Train.prom he _ _ _

lemma four_plus (hx : Stay n U) (h : Stay n V) :
    Outlook.four n (U + V) = Outlook.four n U + Outlook.four n V := by
  funext w
  obtain ⟨x, y⟩ := w
  refine
    congr_fun
      (Lift.unique (H := hereZ n U y x + hereZ n V y x) (live0 (s := y) (y := x) (Stay_add hx h)) ?_)
      0
  rw [page_add]
  exact Lift.add (live0 hx) (live0 h)

lemma four_smul (h : Stay n U) (c : ℂ) : Outlook.four n (c • U) = c • Outlook.four n U := by
  funext w
  obtain ⟨x, y⟩ := w
  refine
    congr_fun (Lift.unique (H := c • hereZ n U y x) (live0 (s := y) (y := x) (Stay_scale h c)) ?_) 0
  rw [page_smul]
  exact Lift.static (live0 h) c

lemma Stay_null (n : ℕ) : Stay n (0 : Flats G) :=
  (Joint.zero (n := n)).toll

lemma Stay_sum (P : Finset I) (H : I → Flats G) (he : ∀ i ∈ P, Stay n (H i)) :
    Stay n (∑ i ∈ P, H i) := by
  classical
    induction P using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact Stay_null n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact Stay_add (he i (by simp)) (ih fun j hj => he j (Finset.mem_insert_of_mem hj))

lemma four_sum (P : Finset I) (H : I → Flats G) (he : ∀ i ∈ P, Stay n (H i)) :
    Outlook.four n (∑ i ∈ P, H i) = ∑ i ∈ P, Outlook.four n (H i) := by
  classical
    induction P using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    ext z l
    rw [Outlook.four, Outlook.no0]
    rfl
  | insert i s hi ih =>
    have hs (j) (h : j ∈ s) := he j (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, four_plus (he i (by simp)) (Stay_sum s H hs),
      ih hs]
end marked
end YM.WilsonMS.HBeam
