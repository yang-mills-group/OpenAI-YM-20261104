import YM.WilsonMS.Stencil.JOptics
import YM.WilsonMS.Calibration.StrongWind
/-!
# Rotating a mark constraint

Part of implementing symmetrized field changes. Subtlety: some of the
invariances of the MS momentum kernels in the high mode proof hold only
on course. Accordingly use the testing hypotheses explicitly.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Trading
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Heat Flux Landau Tone Color Lattice Native Wind Native.Wilsonian Paint Book
  Convolve Program
open Logarithm City LogTime Signal High Menus Lifting Domain Frame Wire Detect Arts Pilot Spin Outlook
  HBeam
open scoped Topology ContDiff Interval
variable {G : Gauge} {h : ℤ} {n k : ℕ} (s : Signed)

abbrev θ (s : Signed) (G : Gauge) : Law G →ₗ[ℂ] Law G :=
  shiftR s G 0
local notation "Z" => θ s G

lemma chore (F : Law G) (l : List (Lane4 G)) : Z F l = SideS s l * F (l.map (permute s)) := by
  unfold θ HBeam.shiftR
  rw [grip0]
  exact hand_index ..

lemma paint_head (t : ℝ) (F : Law G) :
    θ s G (Ccy (Cpu G t) F μzone) = Ccy (Cpu G t) (θ s G F) μzone := by
  funext l
  rw [chore]
  unfold Ccy
  let K := Cpu G t
  rw [← (measureVeh s).integral_comp', ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [at_trc, at_trc, ← Equiv.sum_comp (passN s), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (passN s), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show seat s x = s.act x from rfl, chore, turn_p]
  simp only [List.map_cons, passenger, Signed.act_neg]
  rw [show SideS s ((i, x) :: (j, -x) :: l) = tick s i * (tick s j * SideS s l) from rfl]
  ring

lemma first_only (F V H : Law G) (t : ℝ) (he : ∀ l, net l = 0 → F l = V l) :
    tree parity (Cpu G t) F H = tree parity (Cpu G t) V H := by
  funext l
  apply scatter_congr
  intro i j _
  unfold attaches
  simp only
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [he ((a, -net i) :: i) (by simp), he ((b, -net i) :: i) (by simp)]

private lemma hand_profile (a b : BH G) :
    (leggo G.ColorIndex (hand s)).fieldC a b = if passN s a = b then tick s a else 0 := by
  rcases a with ⟨⟨_ | a, d⟩, i⟩ <;> rcases b with ⟨⟨_ | b, c⟩, j⟩ <;>
    (cases d <;> cases c <;>
            simp only [leggo, rayS, prop, shadow, hand_s, passN, Equiv.prodCongr_apply] <;>
          by_cases he : i = j <;>
        simp [tick, negateField, *])

lemma inTransit (t : ℝ) : Pilot.Transport (flagS (m := 0) (hand s) G) (Cpu G t) (Cpu G t) := by
  let K := Cpu G t
  intro u a b
  obtain ⟨a, rfl⟩ := (passN s).surjective a
  obtain ⟨b, rfl⟩ := (passN s).surjective b
  change
    K _ _ (s.act u) =
      ∑ i : BH G, ∑ j : BH G, K _ _ _ * (leggo _ (hand s)).fieldC _ _ * (leggo _ (hand s)).fieldC _ _
  simp_rw [hand_profile]
  simp
  unfold K
  rw [turn_p]
  ring

lemma onBranch (t : ℝ) (F H : Law G) (hp : SignedScope true F) :
    Z (tree parity (Cpu G t) F H) = tree parity (Cpu G t) F (Z H) := by
  unfold θ HBeam.shiftR
  rw [grip0, (inTransit s t).gatherR _ _ (X_even G t) (X_even G t)]
  refine first_only _ F _ t ?_
  intro l he
  rw [hand_index]
  exact hp s l (fun _ => he)

abbrev shiftF (G : Gauge) (s : Signed) : Wind.Flow G →ₗ[ℂ] Wind.Flow G :=
  LinearMap.pi fun i => (θ s G).comp (LinearMap.proj i)

abbrev moved (G : Gauge) (s : Signed) (F : Wind.Dec G) : Wind.Dec G := fun i p => shiftF G s (F i p)

lemma temper (F : Wind.Flow G) (hx : TouchF F) : TouchF (shiftF G s F) := by
  intro E _ _ f w hw hf
  let L : tagSmooth E (BH G) QP := w.map fun x => (cod s (n := 0) x.1, (grip (n := 0) s).turn ∘ x.2)
  have hL : Trail L := by
    intro i hi
    obtain ⟨x, h, rfl⟩ := List.mem_map.mp hi
    exact ((grip (n := 0) s).turn.toContinuousLinearMap.contDiff).comp (hw x h)
  have he (i : E) :
    shiftF G s F (f i) (walk0 w i) = signs s (walk0 (A := Cfield G 0) w 0) * F (f i) (walk0 L i) := by
    rw [show shiftF G s F (f i) = θ s G (F (f i)) from rfl, θ, HBeam.phase]
    simp only [walk0, L, signs, List.map_map]
    rfl
  simp_rw [he]
  exact ContDiff.mul contDiff_const (hx E f L hL hf)

lemma wireR (F : Wind.Flow G) (hf : TouchF F) (t : ℝ) :
    (Wiref G) (shiftF G s F) t = θ s G ((Wiref G) F t) := by
  change Heat.orbit (Cpu G t) _ (shiftF G s F t) = θ _ _ (Heat.orbit (Cpu G t) _ (F t))
  rw [finite_cc μzone (period0 μzone cour0 (main_f _) (temper s F hf)),
    finite_cc μzone (period0 μzone cour0 (main_f _) hf), paint_head]
  rfl

lemma pose_path {F H : Wind.Dec G} {p : Team} (h : PC G p F) (n : ℕ) (x : ℝ) :
    Wind.path 1 n 0 F (moved G s H) x = shiftF G s (Wind.path 1 n 0 F H x) := by
  funext y
  simp only [Wind.path, one_smul, Finset.sum_apply]
  change ∑ i ∈ Domain.paths n 0, tree parity (Cpu G _) _ _ = θ s G _
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Eq.symm (onBranch s y _ _ (((h.owes (n - i)).stay x).stand y rfl))
variable {F H Q : Dec G} {p : Team} {φ A : Actor G} {j : ℤ}

lemma colourP (h : PC G p F) (hv : PM φ F H j) (ha : PM A F Q j)
    (he : ∀ n x, run (A x n) = θ s G (run (φ x n))) : Q = moved G s H := by
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    funext x
    let U := moved G s H
    obtain hh :=
      Wind.path_eq 1 k 0 (F := F) (H := F) (Q := Q) (W := U) (fun _ _ => rfl)
        (fun j hj => ih j (Wind.path_in hj |>.2))
    let V := Wind.path 1 k 0 F Q x
    have hm : V = shiftF G s (Wind.path 1 k 0 F H x) := Eq.trans (congr_fun hh x) (pose_path s h _ _)
    let N := Q k x
    let M := U k x
    have hN := ha.owes k |>.stay x
    have ht : TouchF (H k x) := ((hv.owes k).stay x).joint
    have hp : TouchF M := temper s (H k x) ht
    have H1 : Sat (run (A x k)) N V := ha.recu ..
    obtain HH := hv.recu k x
    have H2 : Sat (run (A x k)) M V := by
      constructor
      · change θ s G (H k x 0) = _
        rw [he, HH.1]
      intro t w
      have h1 := (HH.2 t (List.map (permute s) w)).const_mul (SideS s w)
      change HasDerivAt (fun t => θ s G (H k x t) w) ((Wiref G (shiftF G s (H k x)) t + V t) w) t
      rw [wireR s _ ht, hm, show shiftF G s (Wind.path 1 k 0 F H x) t = θ s G _ from rfl, ← map_add]
      simp_rw [chore]
      exact h1
    change N = M
    apply sub_eq_zero.mp
    apply Dtotal (F := N - M) ?_ (by rw [Pi.sub_apply, H2.1, H1.1, sub_self])
    obtain ⟨u, hU⟩ := hv.owes k |>.pay
    obtain ⟨v, hV⟩ := ha.owes k |>.pay
    refine
      ⟨fun E _ _ f w h h' => (hN.joint E f w h h').sub (hp E f w h h'),
        ⟨(u + v : ℤ), Rank.sub ((hV x).pay (by omega)) ?_⟩, fun t w _ => ?_⟩
    · intro t w hw
      rw [show M t w = _ from chore s (F := H k x t) w,
        hU x t _
          (by
            simp
            omega),
        mul_zero]
    convert! (H1.2 t w).sub (H2.2 t w) using 1
    rw [map_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
section sums
open Rock Knobs LogTime.IntervalFamily
variable {I : Type} {B D V X : Recount G}

abbrev record (s : Signed) (G : Gauge) (F : Recount G) : Recount G := fun n t => θ s G (F n t)

lemma dim_shift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Wire (BH G) E QP) :
    fieldDim (wfield (A := Axis) (C := G.ColorIndex)) W =
      fieldDim (wfield (A := Arts.L 0) (C := G.ColorIndex)) (shifted s (n := 0) W) := by
  induction W with
  | nil => rfl
  | cons a l ih => rw [shifted, List.map_cons, field_cons, field_cons, ih]

lemma reserve (hX : Fixed V X false h k) : Fixed (record s G V) (record s G X) false h k := by
  intro n hs r h E _ _ w hw hp
  let W := shifted s (n := 0) w
  let L := meet.primary
  have hm : W.length = r := by simp [W, shifted, hp]
  obtain H := hX n hs r h E W (fun i => Bool.noConfusion i) hm
  let c := signs s (sail (A := Cfield G 0) w 0)
  have he (f : Law G) (v : E) : (Z f) (sail w v) = c * f (sail W v) := by
    rw [θ, HBeam.phase, show signs s _ = c from ?_]
    rw [show List.map _ (sail w v) = sail W v from ?_]
    simp only [sail, W, shifted, List.map_map]
    rfl
    simp only [c, sail, signs, List.map_map]
    rfl
  unfold Light
  rw [dim_shift s w]
  convert! Like.L H (ContinuousLinearMap.mul ℝ ℂ c) using 1
  all_goals
    funext i t
    exact he _ _

lemma trust_money (hX : Fixed X V false h k) (c : ℂ) : Fixed (c • X) (c • V) false h k := by
  intro n hn v hv E _ _ w h hs
  exact Like.L (hX n hn v hv E w h hs) (ContinuousLinearMap.mul ℝ ℂ c)

lemma trust_plus (hx : Fixed X V false h k) (hh : Fixed B D false h k) :
    Fixed (X + B) (V + D) false h k := fun n hn r hr E _ _ w hw ht =>
  Like.add (hx n hn r hr E w hw ht) (hh n hn r hr E w hw ht)

lemma trust_sum (s : Finset I) (F H : I → Recount G) (hX : ∀ i ∈ s, Fixed (F i) (H i) false h k) :
    Fixed (∑ i ∈ s, F i) (∑ i ∈ s, H i) false h k := by
  classical
    induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun n _ _ _ => zero_ext (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  | insert i p hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact trust_plus (hX i (by simp)) (ih fun j hj => hX j (Finset.mem_insert_of_mem hj))

lemma coin_zero : PM (0 : Actor G) F 0 j := by
  refine ⟨fun _ => Fees.zero .., fun k x => ⟨(map_zero _).symm, fun t l => ?_⟩⟩
  rw [Pi.add_apply, show Wiref G ((0 : Dec G) k x) t = 0 from congr_fun (map_zero _) t, Wind.path]
  simp only [Pi.zero_apply, one_smul, map_zero, Finset.sum_apply, Finset.sum_const_zero, add_zero]
  exact hasDerivAt_const ..

lemma PMplus (h : PM φ F H j) (hp : PM A F Q j) : PM (φ + A) F (H + Q) j := by
  refine ⟨fun i => Fees.sum2 (h.owes i) (hp.owes i), fun i x => ⟨?_, fun t w => ?_⟩⟩
  · simp only [Pi.add_apply, map_add]
    exact congr_arg₂ (· + ·) ((h.recu i x).1) ((hp.recu i x).1)
  have ht : (path 1 i 0 F (H + Q)) = (path 1 i 0 F H) + (path 1 i 0 F Q) := by
    funext x
    simp only [Wind.path, one_smul, Finset.sum_apply, Pi.add_apply, map_add, sum_add_distrib]
  simp only [ht, Pi.add_apply, map_add]
  rw [add_add_add_comm]
  exact (h.recu i x |>.2 t w).add (hp.recu i x |>.2 t w)

lemma PMscale (h : PM φ F H j) (v : ℝ) : PM ((v : ℂ) • φ) F ((v : ℂ) • H) j := by
  refine ⟨fun i => Fees.fare (h.owes i) v, fun i x => ⟨?_, fun t w => ?_⟩⟩
  · simp only [Pi.smul_apply, map_smul, (h.recu i x).1]
  simp only [Pi.smul_apply, map_smul, Wind.path, one_smul, Finset.sum_apply, Finset.smul_sum]
  convert! (h.recu i x |>.2 t w).const_mul (v : ℂ) using 1
  simp only [Pi.add_apply, Wind.path, one_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.mul_sum]

lemma PMsum (s : Finset I) (a : I → Actor G) (B : I → Dec G) (h : ∀ i ∈ s, PM (a i) F (B i) j) :
    PM (∑ i ∈ s, a i) F (∑ i ∈ s, B i) j := by
  classical
    induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact coin_zero
  | insert b s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact PMplus (h b (by simp)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end sums
end YM.WilsonMS.Trading
