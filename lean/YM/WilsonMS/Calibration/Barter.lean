import YM.WilsonMS.Calibration.Trading
/-!
# Reorienting the spectrum of momentum kernels

Native covariance with D/K under the signed permutations. At any finite
number of legs here. Proofs use the supplied cost calculus, to ensure that
transformations are paid also on the required root expansions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Trading
open Function Filter Set Finset MeasureTheory
open MS Plane Koszul Landau Lattice Cylinder Native Native.Chart Lab Orient Native.Paint Book Convolve
  Program Bare
open Tone Color Native.Draft Wilsonian High Knobs
open Complex (I)
open scoped Topology ContDiff
variable {G : Gauge} {q : ℤ} (s : Signed)
local notation "Γ" => Spectrum G
section native
variable {P : Type} [AddCommGroup P] [One P] {F R : Dot G (Four P)}

lemma bump (hp : Tuned F q) : Tuned (pose s F) q := by
  let W := graffiti (σ s) F
  have hW : Tuned W q :=
    Tune.self_cash hp
      (by
        intro i
        simp [σ])
  refine
    ⟨(ferry_tie (Orient.turn s) (p := field parity) (q := field parity)
            (fun x => (pos_par s x).symm)).sym
        W hW.symm,
      hW.ghost.ferry (v := ghostNo ∘ Prod.fst) _ ?_ _, hW.still.passes _ _⟩
  rintro ⟨⟨⟨_ | a, _ | _⟩, u⟩, x⟩ <;> rfl

lemma commute_d (u : G.El) : pose s (dye u F) = dye u (pose s F) := by
  have hx : ∀ V : Dot G (Four P), graffiti (σ s) (dye u V) = dye u (graffiti (σ s) V) := by
    let K := σ s (P := Four P) (G := G)
    intro V
    apply Subtype.ext
    funext l
    have he (l : List (LightMode G (Four P))) (v : Film G (Four P)) :
      repeatC u (Cylinder.rent K v) l = (l.map K).prod * repeatC u v l := by
      induction l generalizing v with
      | nil => simp [Cylinder.rent]
      | cons a l ih =>
        rw [repeat_cons, repeat_cons, List.map_cons, List.prod_cons, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show D (setLeg a i) (Cylinder.rent K v) = (K a) • Cylinder.rent K (D (setLeg a i) v) from
            funext fun l => mul_assoc ..,
          map_smul, Pi.smul_apply, ih]
        rw [smul_eq_mul]
        ring
    rw [landc, dye_rep, dye_rep, landc]
    exact (he l _).symm
  unfold pose
  rw [LinearMap.comp_apply, hx]
  let r (x : Atom Axis × Four P) : Atom Axis × Four P :=
    match x with
    | ((none, d), p) => ((none, d), s.act p)
    | ((some a, d), p) => ((some (s.perm a), d), (purse s (p, a)).1)
  exact paint_pass _ u _ (Orient.turn s) r (by rintro ⟨⟨_ | a, _ | _⟩, b⟩ i <;> rfl) _

lemma keepsInk (h : Colorless F) : Colorless (pose s F) := by
  intro i
  rw [← commute_d, h]

lemma slimmer (h : Limit F.val q) : Limit (pose s F).val q := by
  apply Limit.shades _ _ _
  exact fun l he => by
    rw [landc]
    change _ * F.val l = 0
    rw [h l he, mul_zero]

lemma halfLaw (F : Dot G (Four P)) (i : LightMode G (Four P)) :
    enter (Orient.turn s i) (pose s F) = σ s i • pose s (enter i F) := by
  have hx : Injective (Orient.turn (R := P) (G := G) s) := (axise s).injective
  unfold pose
  rw [LinearMap.comp_apply, ferry_units (Orient.turn s) _ hx, tagged_s, map_smul]
  rfl

omit [AddCommGroup P] [One P] in
lemma casts (i : ToneS G) (x : Four P) :
    let k := (Γ).dual i;
    let v := (Γ).plain i;
    σ s (v, x) * σ s (k, x) = 1 := by
  rcases i with ⟨a, i⟩ | b
  cases hv : s.flip a <;> simp [σ, fee, signA, Spectrum, leggin, signA, hv]
  simp [σ, fee, Spectrum, leggin, signA]

lemma signal (b : Bool) : twisted DotFlip b (pose s F) = pose s (twisted DotFlip b F) := by
  unfold pose
  simp_rw [LinearMap.comp_apply, ←
    ferry_twist (r := Orient.turn s) (p := field parity) (fun x => Eq.symm (pos_par s x)), tag_sign]
section finite
variable [Fintype P]

def pathG : Equiv.Perm (ToneS G) :=
  (Equiv.sumCongr (Equiv.prodCongr s.perm (Equiv.refl G.ColorIndex)) (Equiv.refl G.ColorIndex))

def lamp0 (v : ToneS G) : Equiv.Perm (Four P) :=
  match v with
  | Sum.inr _ => s.actEquiv.toEquiv
  | Sum.inl (a, _) => (s.actEquiv.toEquiv).trans (Equiv.addRight (shiftTerm s a))

omit [Fintype P] in
lemma goes (v : ToneS G) (x : Four P) :
    Orient.turn s ((Γ).dual v, x) = ((Γ).dual (pathG s v), lamp0 s v x) ∧
      Orient.turn s ((Γ).plain v, x) = ((Γ).plain (pathG s v), lamp0 s v x) :=
  by rcases v with ⟨a, j⟩ | _ <;> exact ⟨rfl, rfl⟩

lemma lampK (F : Dot G (Four P)) : (Γ).Lap (pose s F) = pose s ((Γ).Lap F) := by
  rw [Bonded.lap_at, Bonded.lap_at, map_sum, ← Equiv.sum_comp (pathG s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, show ((Γ).fee _ : ℂ) = (Γ).fee i from ?_]
  swap
  · rcases i with ⟨_, _⟩ | i <;> rfl
  congr 1
  rw [heart_all, heart_all, map_sum, ← Equiv.sum_comp (lamp0 s i)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← (goes s i x).1, ← (goes s i x).2, halfLaw, map_smul, halfLaw, smul_smul, mul_comm (σ s _) _,
    casts, one_smul]

lemma guide : pose s ((Γ).touch F R) = (Γ).touch (pose s F) (pose s R) := by
  let Z : On (Branch G Axis) (Four P) ℂ := (Γ).Lap
  have he (F H : Dot G (Four P)) :
    (Γ).touch F H =
      (Z (couple DotFlip (sumHome F) H) - couple DotFlip (Z (sumHome F)) H) -
        couple DotFlip (twisted DotFlip true (sumHome F)) (Z H) := by
    apply Subtype.ext
    simp only [Bonded.t_here, Z, Bonded.lap_here, coupled, twistp, Submodule.coe_sub, link]
  rw [he, he]
  unfold Z
  rw [map_sub, map_sub, ← lampK, pose_s, pose_s, pose_s, ← lampK, ← signal, ← lampK, ← moving_total]
end finite
end native
variable {U F H : Dot G Cover}

lemma lamp (F : Dot G Cover) : pose s ((Γ).Lap F) = (Γ).Lap (pose s F) := by
  refine (markEq ..).mp ?_
  filter_upwards [soon_heart (Γ) (pose s F), soon_heart (Γ) F] with n h hn
  rw [h, travel_t, hn, travel_t, lampK]

lemma guide_stood (h : stance F) : pose s ((Γ).touch F H) = (Γ).touch F (pose s H) := by
  refine (markEq ..).mp ?_
  have hp := h s
  filter_upwards [soon_root (Γ) F (pose s H), soon_root (Γ) F H, hp] with n h he ht
  rw [travel_t, he, guide, h, travel_t]
  apply Subtype.ext
  rw [Bonded.t_here, Bonded.t_here]
  change (link _ _ _ (sumHome (pose s (shown n F))).val _) = _
  rw [← travel_t, show (sumHome (shown n (pose s F))).val = _ from ht]
  rfl
open HBeam Arts

lemma θ_inv (f : Landau.Detect.Law G) : θ s G (θ s⁻¹ G f) = f := by
  let F : Arts.Mob G := fun
    | 0 => f
    | _ + 1 => (fun _ => 0)
  have hp := sequence s s⁻¹ F
  rw [inv_mul_cancel, headed] at hp
  exact congr_fun hp 0

lemma pose_run (X : Dot G Cover) : run (pose s⁻¹ X) = θ s G (run X) := by
  let K := θ s G
  let L := θ s⁻¹ G
  let W := pose s⁻¹ X
  have hh : L (run W) = run X := by
    funext l
    rw [show L _ _ = _ from Trading.chore s⁻¹ (run W) l, show run W _ = _ from Tone.by_shift s⁻¹ X l]
    rw [← mul_assoc, City.twice_S, one_mul]
  rw [← hh]
  exact (θ_inv ..).symm

lemma pose_train (p : Team) (x : ℝ) (k : ℕ) (f : Dot G Cover) :
    pose s (train (fieldV p x ∘ Prod.fst) k f) = train (fieldV p x ∘ Prod.fst) k (pose s f) := by
  let V : Branch G Axis → _ := fieldV p x
  have hb (j : LightMode G Cover) : V (Orient.turn s j).1 = V j.1 := by
    rcases j with ⟨⟨⟨_ | j, t⟩, u⟩, x⟩ <;> rfl
  have hc :
    graffiti (σ s) (train (fieldV p x ∘ Prod.fst) k f) = train (V ∘ Prod.fst) k (graffiti (σ s) f) :=
    Subtype.ext (funext fun _ => mul_left_comm ..)
  unfold pose
  rw [LinearMap.comp_apply, hc]
  exact
    pennant_ferry (Orient.turn s) (PowerSeries.coeff k) (V ∘ Prod.fst) (V ∘ Prod.fst)
      (fun t => (hb t).symm) _

lemma pose_wobble (v : T (Dot G Cover)) (p : Team) (x : ℝ) (k : ℕ) :
    pose s (wobble G p x v k) = wobble G p x (promote (pose s) v) k := by
  unfold wobble
  simp only [LinearMap.comp_apply, rolls, map_sum, pose_train]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← comm (L := pose s)]
  rfl
end YM.WilsonMS.Trading
