import YM.WilsonMS.Stencil.JShift
/-!
# Freeze the MS basis of physical open-index marks

For the `Ensure` physical space of radial jets the Jrad optical formula
specifies a lift to MS curvature-derivative local inputs. These are written
BEFORE any position renormalization. See `literature` for the `Mach.Ele`
verification at birth.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.JRad
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Rock _root_.YM.MS.Shine Outlook
open Labels Analysis Tensor Maxwell Motif Halo Mach Lifting Theater HBeam Detect Detect.Mark Local.BV
  InnerProductSpace
open Garment Color Submodule
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {m n k i j : ℕ} {z : ℂ}
section raw

abbrev Script (G : Gauge) :=
  ℂ → Mob G

def ChartW (G : Gauge) (k h : ℕ) : Set (Script G) :=
  {x | ∃ f : Fin k → Plaq, ∃ σ : Lifting.Grid G k, Pole.wage k f = h ∧ x = Pole.wing k f σ}

def Words (G : Gauge) (k h : ℕ) :=
  Submodule.span ℝ (ChartW G k h)
variable {F H : Script G}

lemma word (h : F ∈ ChartW G m k) : F ∈ Words G m k :=
  Submodule.subset_span h

lemma signsK (h : F ∈ Words G i j) : ∀ z n, Pure (field parity) false (F z n) := by
  refine
    Submodule.span_induction (R := ℝ) (s := ChartW G i j) (p := fun F _ =>
      ∀ (z : ℂ) (n : ℕ), Pure (field parity) false (F z n)) ?_ (fun _ _ => Pure.zero)
      (fun x y _ _ h hv z t => Pure.add (h z t) (hv z t))
      (fun c _ _ hy z t => Pure.smul (c : ℂ) (hy z t)) h
  rintro f ⟨a, u, rfl, rfl⟩ z n
  exact (Pole.prepared ..).even

lemma word_ray (x : E4) (i : ℕ) (a : Axis) (c : G.ColorIndex) :
    factor G i (reading G i x a c) ∈ Words G 1 (i + 2) := by
  let f (j : Axis) (l : Fin i → Axis) : Script G := fun z n => Pole G n j a z (List.ofFn l) c
  have hm (j l) : f j l ∈ ChartW G 1 (i + 2) := by
    let p : Plaq := ⟨j, a, List.ofFn l⟩
    refine ⟨(fun _ => p), (fun _ => c), ?_, ?_⟩
    · simp only [Pole.wage, p, Pole.Grit, List.length_ofFn]
      simp [add_comm 2]
    ext z n l
    exact congr_fun (closeAt (Mach.Pole_leaf (G := G) (n := n) z p c)).symm l
  have he :
    factor G i (reading G i x a c) =
      volume i • ∑ j : Axis, (x j : ℝ) • ∑ k : Fin i → Axis, (∏ j : Fin i, x (k j)) • f j k := by
    funext z n l
    rw [corresponding]
    simp only [node, ray_sum, Pi.smul_apply, Finset.sum_apply]
    rfl
  rw [he]
  exact
    smul_mem _ _ (sum_mem fun j _ => smul_mem _ _ (sum_mem fun k _ => smul_mem _ _ (word (hm j k))))

lemma word_f (g : Module.Dual ℝ (Labels.Taylor G i)) : factor G i g ∈ Words G 1 (i + 2) := by
  let T := Submodule.comap (factor G i) (Words G 1 (i + 2))
  suffices he : ⊤ ≤ T from he (x := g) mem_top
  rw [← JRad.enough, span_le]
  rintro f ⟨x, a, c, rfl⟩
  exact word_ray x i a c

lemma word_p (h : F ∈ Words G i j) : Present F := by
  refine
    Submodule.span_induction (R := ℝ) (p := fun f _ => Present f) ?_ (Present.here 0)
      (fun _ _ _ _ => Present.add) (fun c x _ ht => ht.smul (c : ℂ)) h
  rintro f ⟨p, q, rfl, rfl⟩
  exact Pole.Presence ..

private def typ (G : Gauge) : Script G →ₗ[ℝ] Script G →ₗ[ℝ] Script G :=
  LinearMap.mk₂ ℝ (fun a b z n => bite n G (a z n) (b z n))
    (fun A B C => funext fun k => funext fun i => map_add ((bite i G).flip (C k i)) (A k i) (B k i))
    (fun t A B => funext fun k => funext fun i => LinearMapRealm ((bite i G).flip (B k i)) (A k i) t)
    (fun A B C => funext fun k => funext fun i => map_add (bite i G (A k i)) (B k i) (C k i))
    (fun t A B => funext fun k => funext fun i => LinearMapRealm (bite i G (A k i)) (B k i) t)

lemma prefixF (hp : F ∈ Words G 1 n) (ht : H ∈ Words G i j) :
    (fun z m => bite m G (F z m) (H z m)) ∈ Words G (i + 1) (n + j) := by
  let V := Words G (i + 1) (n + j)
  let S := typ G
  suffices he : Words G 1 n ≤ Submodule.comap (S.flip H) V from he hp
  rw [Words, span_le]
  rintro F ⟨p, q, rfl, rfl⟩
  suffices hm : Words G i j ≤ Submodule.comap (S (Pole.wing 1 p q)) V from hm ht
  rw [Words, span_le]
  rintro H ⟨a, b, rfl, rfl⟩
  let x : Fin (i + 1) → Plaq := Fin.cons (p 0) a
  let y : Lifting.Grid G (i + 1) := Fin.cons (q 0) b
  apply word
  refine ⟨x, y, ?_, ?_⟩
  · simp only [x, Pole.wage_add, Fin.cons_zero,
      show x ∘ Fin.succ = a from
          (by
            funext i
            simp [x])]
    simp [Pole.wage]
  funext z n
  change bite n G (Pole.wing 1 p q z n) (Pole.wing i a b z n) = _
  have hc :=
    closeAt (p := field (P := SectorP n) (parity (C := G.ColorIndex))) (Pole_leaf z (p 0) (q 0))
  rw [show Pole.wing 1 p q z n = Pole_leaf z (p 0) (q 0) from hc]
  simp only [Pole.wing, prodS, x, y, Fin.cons_zero, Function.comp_def, Fin.cons_succ]

lemma wordC (c : ℝ) : (fun (_ : ℂ) n => coin (A := Shore G n) (c : ℂ)) ∈ Words G 0 0 := by
  let F := Pole.wing 0 (fun i => i.elim0) (G := G) (fun i => i.elim0)
  have he : F ∈ ChartW G 0 0 := ⟨_, _, by simp [Pole.wage], rfl⟩
  have hp : c • F = fun (_ : ℂ) n => coin (A := Shore G n) (c : ℂ) := by
    funext i n l
    cases l <;> change (c : ℂ) * _ = _
    exact mul_one _
    exact mul_zero _
  rw [← hp]
  exact smul_mem _ _ (word he)

abbrev Tagged (g : G.El) (z : ℂ) (n : ℕ) (l : Legs (Shore G n)) (F : Script G) :=
  repeatC g (F z n) l

lemma meanM (h : F ∈ Words G i j) :
    (∀ z n l, Integrable (fun g : G.El => Tagged g z n l F) G.probHaar) ∧
      (fun z n l => ∫ g : G.El, Tagged g z n l F ∂G.probHaar) ∈ Gallery G i j := by
  let T (f : Script G) : Script G := fun z n l => ∫ g : G.El, Tagged g z n l f ∂G.probHaar
  refine
    Submodule.span_induction (p := fun f _ =>
      (∀ z n l, Integrable (fun g : G.El => Tagged g z n l f) G.probHaar) ∧ T f ∈ Gallery G i j) ?_ ?_
      ?_ ?_ h
  · rintro f ⟨a, b, rfl, rfl⟩
    let K := Pole.wing i a b
    let Φ (c : Lifting.Grid G i) := Pole.wing i a c
    have hw (g : G.El) (z : ℂ) (n : ℕ) l :
      Tagged g z n l K = ∑ j : Lifting.Grid G i, (Lifting.ink g j b) • Φ j z n l := by
      unfold Tagged
      rw [Pole.radiant i a b g]
      simp only [Finset.sum_apply, Pi.smul_apply]
      rfl
    have hc (c : Lifting.Grid G i) (x : ℂ) :
      Integrable (fun g : G.El => Lifting.ink g c b • x) G.probHaar := (massInk c b).smul_const _
    refine
      ⟨fun z n l => by
        change Integrable (fun g => Tagged g z n l K) G.probHaar
        simp_rw [show ∀ g, Tagged g z n l K = _ from fun g => hw g z n l]
        exact integrable_finsetSum _ fun k _ => hc k _, ?_⟩
    rw [show T K = Pole.saint i a b from ?_]
    · exact Submodule.subset_span (mem_setOf.mpr ⟨a, b, rfl, rfl⟩)
    funext z n l
    unfold T
    simp_rw [hw]
    rw [integral_finsetSum _ (fun i _ => hc i _)]
    simp only [integral_smul_const, Pole.saint, Finset.sum_apply, Pi.smul_apply]
    rfl
  · have ht : T 0 = 0 := by
      ext
      simp [T, Tagged]
    refine ⟨fun _ _ _ => by simp [Tagged], (?_)⟩
    rw [ht]
    exact zero_mem _
  · rintro x y _ _ ⟨hX, h⟩ ⟨hY, H⟩
    have hv (g : G.El) z n l : Tagged g z n l (x + y) = Tagged g z n l x + Tagged g z n l y :=
      congr_fun (map_add (repeatC g) (x z n) (y z n)) l
    refine ⟨fun z n l => ?_, ?_⟩
    · simp_rw [hv]
      exact Integrable.add (hX z n l) (hY z n l)
    rw [show T (x + y) = T x + T y from
        funext
          (fun z =>
            funext fun n =>
              funext fun l => by
                change (∫ g, Tagged g z n l (x + y) ∂_) = _
                simp_rw [hv]
                exact integral_add (hX z n l) (hY z n l))]
    exact add_mem h H
  rintro c f _ ⟨hx, h⟩
  have ht (g : G.El) z n l : Tagged g z n l (c • f) = c • Tagged g z n l f :=
    congr_fun (LinearMapRealm (repeatC g) (f z n) c) l
  refine ⟨fun z n l => ?_, ?_⟩
  · simp_rw [ht]
    exact Integrable.smul c (hx z n l)
  rw [show T (c • f) = c • T f from ?_]
  exact smul_mem _ _ h
  funext z n l
  unfold T
  simp_rw [ht, integral_smul]
  rfl

lemma gallery_of (h : F ∈ Words G i j) (H : ∀ z, ShadeG (F z)) : F ∈ Gallery G i j := by
  obtain ⟨T, hV⟩ := meanM h
  have hp (z : ℂ) (n : ℕ) (l) : (∫ g : G.El, Tagged g z n l F ∂G.probHaar) = F z n l := by
    simp only [Tagged, H z n _]
    simp
  simp_rw [hp] at hV
  exact hV
end raw
section frame

abbrev φ (a : Labels.Key G) :=
  (axes G a.1).coord a.2

abbrev member (a : Labels.Key G) :=
  factor G a.1 (φ a)

abbrev ZK (G : Gauge) (n : ℕ) :=
  field (P := SectorP n) (Landau.parity (A := Arts.L n) (C := G.ColorIndex))

def plate (a : Labels.Key G) (z : ℂ) (n : ℕ) : ↥(Theater.Dark (ZK G n)) :=
  ⟨member a z n, signsK (word_f (φ a)) z n⟩

def name (G : Gauge) (z : ℂ) (n : ℕ) : Labels.Pol G →ₐ[ℂ] ↥(Theater.Dark (ZK G n)) :=
  MvPolynomial.aeval (fun i => plate i z n)

def optic (G : Gauge) : Pol G →ₗ[ℂ] Script G
    where
  toFun f z n := name G z n f |>.val
  map_smul' c
    f :=
    funext fun z =>
      funext fun n =>
        congr_arg (fun x : ↥(Theater.Dark (ZK G n)) => x.val) (map_smul (name G z n) c f)
  map_add' x y := funext fun z => funext fun n => congr_arg Subtype.val (map_add (name G z n) x y)

lemma constV (c : ℂ) : optic G (MvPolynomial.C c) z n = Koszul.coin c := by
  change (name G _ _ _).val = _
  rw [name, MvPolynomial.aeval_C]
  exact cash1 ..

lemma names (a : Labels.Key G) : optic G (MvPolynomial.X a) = member a :=
  funext fun z =>
    funext fun i => congr_arg Subtype.val (MvPolynomial.aeval_X (fun i' => plate i' z i) a)

lemma productV (a b : Pol G) : optic G (a * b) z n = bite n G (optic G a z n) (optic G b z n) := by
  change (name G z n (a * b)).val = _
  rw [map_mul]
  rfl

open MvPolynomial in
lemma monName (c : ℝ) (u : Key G →₀ ℕ) :
    optic G (MvPolynomial.monomial u (c : ℂ)) ∈
      Words G ((Finsupp.weight bidegree u).2) ((Finsupp.weight bidegree u).1) := by
  apply Extra.FD.per_factor (ι := Key G) u
  · rw [map_zero]
    change optic G (C (c : ℂ)) ∈ Words G 0 0
    rw [show optic G (C (c : ℂ)) = fun _ n => coin (A := Shore G n) (c : ℂ) from
        funext fun _ => funext fun _ => constV _]
    exact wordC c
  intro i a h
  let F (a : Key G) := MvPolynomial.X (R := ℂ) a
  rw [map_add, Finsupp.weight_single, monomial_add_single, pow_one, mul_comm _ (X a)]
  simp only [one_smul]
  change optic G ((F a) * _) ∈ Words G (_ + 1) (_ + (a.1 + 2))
  rw [add_comm _ (a.1 + 2)]
  rw [show optic G ((F a) * _) = _ from
      (funext (fun z : ℂ => funext (fun n : ℕ => productV (z := z) (n := n) _ _)))]
  unfold F
  rw [names]
  exact prefixF (word_f (φ a)) h

lemma load (v : Pol G) (he : Labels.conjPol v = v) (h : At v (i, j)) : optic G v ∈ Words G j i := by
  have ht (u : Key G →₀ ℕ) : ∃ c : ℝ, MvPolynomial.coeff u v = (c : ℂ) := by
    have hp := congr_arg (MvPolynomial.coeff u) he
    simp only [Labels.conjPol, MvPolynomial.coeff_map] at hp
    obtain ⟨c, hc⟩ := Complex.conj_eq_iff_real.mp hp
    exact ⟨c, hc⟩
  rw [MvPolynomial.as_sum v, map_sum]
  refine sum_mem fun k hh => ?_
  obtain ⟨c, hc⟩ := ht k
  rw [hc]
  obtain he := monName (G := G) c k
  rwa [(nodeId .. |>.mp h) (MvPolynomial.mem_support_iff.mp hh)] at he

lemma shaped (i : ℕ) (f : Module.Dual ℝ (Labels.Taylor G i)) :
    optic G (Theater.page i (Complex.ofRealCLM.toLinearMap.comp f)) = factor G i f := by
  have ht : f = ∑ j, f ((axes G i) j) • (axes G i).coord j := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sum_apply]
    nth_rw 1 [← (axes G i).sum_repr x]
    simp_rw [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => mul_comm ..
  unfold page
  simp_rw [map_sum, map_smul, LabelC, names]
  conv_rhs => rhs; rw [ht]
  rw [map_sum]
  simp_rw [map_smul]
  rfl

lemma changedK (u : (i : ℕ) → Module.End ℝ (Labels.Taylor G i)) (a : Key G) :
    optic G (changed u (MvPolynomial.X a)) = factor G a.1 ((φ a).comp (u a.1)) := by
  change optic G (changed u (LabelC a)) = _
  rw [Theater.moved_v]
  exact shaped a.1 ((φ a).comp (u a.1))

lemma firstSeen (p : Pol G) : optic G p 0 0 = Theater.orbit G p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [constV, cus]
  | mul_X v a ih =>
    rw [productV, names, bags, ih, cusp, show member a 0 0 = _ from first_line (f := φ a)]
  | add p q hp hq => rw [map_add, map_add, Pi.add_apply, Pi.add_apply, hp, hq]

lemma signedK (p : Pol G) (s : Signed) :
    (fun i => rotateMob s G (optic G p i)) = optic G (changed (fun _ => Taylor.turn s.ortho) p) := by
  let S (i : ℕ) := Labels.Taylor.turn (G := G) (j := i) s.ortho
  let T := changed S
  induction p using MvPolynomial.induction_on with
  | C a =>
    unfold changed
    simp_rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    funext i n
    change shiftR s G n _ = _
    rw [constV]
    exact (raised s n G).fixC _
  | mul_X v a ih =>
    rw [map_mul (changed S)]
    funext i n
    change shiftR s G n _ = _
    rw [productV, productV, names,
      show shiftR s G n _ = _ from ((raised s n G).prod (optic G v i n) (member a i n)),
      show (raised s n G).run _ = _ from congr_fun (congr_fun ih i) n,
      show (raised s n G).run (member a i n) = _ from congr_fun (congr_fun (factors s (φ a)) i) n,
      changedK]
  | add a b ha hb =>
    simp_rw [map_add, Pi.add_apply, map_add, congr_fun ha, congr_fun hb]
    rfl

lemma cardK (p : Pol G) (s : G.El) (z : ℂ) (n : ℕ) :
    repeatC s (optic G p z n) = optic G (changed (fun _ => Labels.Taylor.paint s) p) z n := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    unfold changed
    simp_rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, constV, Safe.cpig]
  | mul_X v a ih =>
    rw [map_mul (changed (G := G) (fun _ => Labels.Taylor.paint s)), productV, productV, names,
      glob_prod, ih, show repeatC s (member a z n) = _ from stamps (φ a) s z n, changedK]
  | add x y hx hy => simp_rw [map_add, Pi.add_apply, map_add, hx, hy]

lemma work0 {v : Pol G} (h : v ∈ Film0 G i j) : optic G v ∈ Gallery G j i := by
  obtain ⟨hu, hp, he⟩ := (cinema v).mp h
  refine gallery_of (JRad.load v he hu) ?_
  intro z n g
  rw [cardK, show changed (fun _ => Labels.Taylor.paint g) v = v from ?_]
  apply Labels.eval_ext
  intro A
  rw [eval_changed]
  exact hp A g
open Menus Local.Physical

lemma literature {v : Pol G} (h : v ∈ Film0 G i j) :
    ∃ X : Literal.Box (Mob G),
      (fun z => Literal.value (Mob G) z X) = optic G v ∧ Ele i j (Theater.orbit G v) X := by
  obtain ⟨V, hV⟩ := word_p (load v ((cinema v |>.mp h).2.2) ((cinema v |>.mp h).1))
  refine ⟨V, hV, ?_, ?_⟩
  · rw [hV]
    exact work0 h
  rw [show V 0 0 = Literal.value (Mob G) 0 V 0 from ?_,
    show Literal.value (Mob G) 0 V = _ from congr_fun hV 0]
  exact firstSeen v
  exact congr_fun (Literal.low_row V).symm 0
open Land
variable (G)
local notation "B" => Ensure.deck G

private abbrev blink {d : ℕ} (i : Plaid B d) :
    Theater.orbit G (ΕData B (Land.read i)) = (Land.read i |>.read) :=
  lamp_here B i.2

def book : Booked (Ensure.deck G) :=
  { optics d i := (literature (filmW B (h := d) i.2)).choose
    law d
      i :=
      (blink G i) ▸
        (show Ele d i.fst.val (Theater.orbit G _) ((literature (filmW B (h := d) i.2)).choose) from
          (literature (filmW B (h := d) i.2)).choose_spec.2) }

lemma Book_formula (d : ℕ) (i : Plaid (Ensure.deck G) d) (z : ℂ) :
    Literal.value _ z ((book G).optics d i) = optic G (Theater.ΕData _ (Land.read i)) z :=
  congr_fun (literature (filmW B (h := d) i.2)).choose_spec.1 z
end frame
end YM.WilsonMS.JRad
