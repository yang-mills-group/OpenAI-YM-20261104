import YM.WilsonMS.Scales.Fuels
/-!
# Log-Polynomial flow of position coupling and adjusted field clock

Still in X-space. Scale law after $\mathrm{eqConv}$ conjugation follows at
the same testing points; working with only fixed positions allowed. Exponent
budgets separate. Punctured compact tests only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
namespace Raha
variable {V : Store G} (P : Rose.Pick V) {F : Scheme G}
variable {M : Booked (Ensure.deck G)} (T : MS_Data G M)

private lemma meritS {S : Set (Points n)} {F : ℝ → S → Point G d n}
    (h : ∀ p : Fin n → Sec G d, Ready (fun v => fun i => F v i p)) (a : ℝ → Fin n → Sec G d)
    (hv : ∀ i, Ready (fun v => a v i)) : Ready (fun v => fun i => F v i (a v)) := by
  let B := Daylight BΨ d
  let W (i : Fin n → Glyph BΨ d) (t : ℝ) := ∏ j : Fin n, B.coord (i j) (a t j)
  let V i (t : ℝ) : S → ℂ := fun k => W i t * F t k (glow ∘ i)
  have he : Ready (∑ i : Fin n → Glyph BΨ d, V i) := by
    refine
      Ready.sums Finset.univ fun i _ =>
        Ready.pair (Algebra.lmul ℝ (S → ℂ)).toLinearMap (f := fun t (_ : S) => W i t) ?_
          (h (glow ∘ i))
    have hx : Ready (W i) :=
      cart_card _ fun j _ => Ready.linear (hv j) ((B.coord _).restrictScalars ℝ)
    exact hx.linear (LinearMap.pi fun _ : S => LinearMap.id (R := ℝ) (M := ℂ))
  rw [show (fun p : ℝ => fun i => F p i (a p)) = ∑ i : Fin n → Glyph BΨ d, V i from ?_]
  · exact he
  funext v i
  simp only [Finset.sum_apply]
  exact fromHeight ..

lemma thawCheck (V : Store G) (s : Set (Points n)) (h : IsCompact s) (hp : s ⊆ conf n)
    (v : Fin n → Sec G d) (j : ℕ) : Ready (fun r : ℝ => fun x : s => Gates.Thaw V T r d x.val j v) := by
  unfold Gates.Thaw
  simp_rw [pivot_cost]
  rw [show
      (fun r : ℝ => fun x : s =>
          ∑ i ∈ Normalize.tally j n,
            lowKernel T r (i none) d x.val (pulseU i (deck (Lμ V T r d)) v)) =
        (∑ i ∈ Normalize.tally j n, fun r : ℝ => fun x : s =>
          lowKernel T r (i none) d x.val (pulseU i (deck (Lμ V T r d)) v))
      from ?_]
  swap
  · funext i p
    simp_rw [Finset.sum_apply]
  apply Ready.sums _
  intro i hi
  exact
    meritS (fun p => fuelM T s h hp p _) (fun r => pulseU i _ v)
      (fun k => shellship (track_mem (T := fun r => Lμ V T r d) (clockPoly T V _ _)) (v k))

private lemma readProd {I : Type} {F H : ℝ → I → Cn}
    (h : ∀ i, Ready (fun x => fun j => coeff i (F x j)))
    (ht : ∀ i, Ready (fun x => fun j => coeff i (H x j))) (i : ℕ) :
    Ready (fun x => fun j => coeff i (F x j * H x j)) := by
  let E (p : ℕ × ℕ) (x : ℝ) (j : I) := coeff p.1 (F x j) * coeff p.2 (H x j)
  have he : Ready (∑ p ∈ Finset.antidiagonal i, E p) :=
    Ready.sums _ (fun p _ => Ready.pair (Algebra.lmul ℝ (I → ℂ)).toLinearMap (h p.1) (ht p.2))
  convert he using 1
  ext1 x
  ext1 p
  simp_rw [PowerSeries.coeff_mul, Finset.sum_apply]
  rfl

lemma pulseμ (j : ℕ) : Ready (fun v => coeff j (FrameConj.χMS v P T)) := by
  by_cases hj : j = 0
  · subst j
    simp_rw [show ∀ x : ℝ, coeff 0 (χMS x P T) = 0 from fun i => built0 ..]
    exact Ready.const _
  unfold FrameConj.χMS
  simp_rw [takes P _ j hj]
  let f := Rose.test P
  let U := tsupport f
  let Q (t : ℝ) (p : Points 3) := plays (Thaw V T t 6) p
  refine Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (Ready.const _) ?_
  change Ready (fun x => f.applyTo fun p => coeff j (Q x p))
  let M x (y : U) := coeff j (Q x y.val)
  have he : Ready M := by
    have hp i (j : ℕ) :
      Ready (fun v : ℝ => fun x : U => coeff j (Rose.batchT (Thaw V T v 6 x.val) i)) := by
      unfold Rose.batchT
      simp_rw [PowerSeries.coeff_mk]
      exact thawCheck T V _ f.hasCompactSupport f.tsupport_subset _ j
    unfold M Q plays Rose.b3
    simp_rw [map_add, two_smul, map_add, map_sub]
    let H := (readProd (H := _) (readProd (hp {0}) (hp { 1 })) (hp { 2 }) j)
    exact
      Ready.add
        (Ready.sub (hp _ _)
          (((readProd (hp _) (hp _) _).add (readProd (hp _) (hp _) _)).add
            (readProd (hp _) (hp _) _)))
        (H.add H)
  obtain ⟨m, hM⟩ := he
  let Vμ t (x : Points 3) := coeff j (Q t x)
  let u (t : ℝ) := f.applyTo (Vμ t)
  have hh (t) : u t = evaluate m u t := by
    have hx (x : Points 3) :
      f x * Vμ t x = ∑ i ∈ Finset.range m, (plate m i).eval t • (f x * Vμ i x) := by
      by_cases h : x ∈ U
      · obtain he := congr_fun (interpret hM t) (show U from ⟨x, h⟩)
        simp only [evaluate, Finset.sum_apply, Pi.smul_apply] at he
        rw [show Vμ t x = _ from he, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_smul_comm ((plate m i).eval t) (f x) _
      rw [image_eq_zero_of_notMem_tsupport h]
      simp
    unfold u evaluate Test.applyTo
    simp_rw [hx]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · simp_rw [integral_smul]
    exact (f.smearing (FrameConj.tender (Gates.theorem_F V i T 6 3) j)).smul ((plate m i).eval t)
  change Ready u
  rw [funext hh]
  exact eval_ready ..

lemma transit_coin (j : ℕ) : Ready (fun v => coeff j (transit P T v)) := by
  unfold transit
  simp_rw [usePool (c := ψW P T) (Ice.born ..)]
  apply accounts
  intro i _
  exact
    Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (Ready.const _)
      (coord_apply
        (by
          have hk := Ready.got Polynomial.X
          have hv : Ready (fun x : ℝ => x) := (by simpa using hk)
          exact hv.neg)
        (pulseμ _ _ i))
section chart
variable {W : Initialize G} {Q : Prescription (Ensure.deck G)}

include P

lemma cashComp (t : ℝ) (hG : G.Simple) (hp : Installed W T Q) (hq : Commuting Q) (d : ℕ) :
    Zx P T d * β_frame P T t d =
      coupon (ψW P T) (KnotMS T V (-t) d) * coupon (transit P T t) (uprightN P T d) := by
  let S := uprightN P T d
  let B := FrontMS P T d
  let W := buryD t B
  let X := coupon (ψW P T) (KnotMS T V (-t) d)
  let Q := compass t (transit P T t) (W |> fun k => vault k * X) S
  have he : changeM P T t d = vault W * X := rfl
  change Zx P T d * Q = _
  have hZ := congr_fun (recallZ P hG hp hq) d
  rw [← paceM (A := Zx P T d) t Mass.print, hZ, wedge, mul_assoc]
  change W * (buryD t S * Q) = _
  rw [←
    show changeM P T t d * coupon _ S = buryD t S * Q from
      turning t (transit P T t) (freeN P hG hp hq d)]
  rw [he]
  change W * (vault W * X * _) = _
  rw [← mul_assoc, ← mul_assoc, (antidote (Oven P hG hp hq)).1, one_mul]
end chart

lemma ticket_align (d j : ℕ) : Ready (fun t : ℝ => coeff j (coupon (ψW P T) (KnotMS T V (-t) d))) := by
  simp_rw [coupon, PowerSeries.coeff_mk, rules]
  apply accounts
  intro i _
  let L := -(0 : ℝ)
  have he : Ready (fun t : ℝ => coeff i (KnotMS T V (-t) d)) := by
    obtain hh := (coord_burn (track_mem (T := fun v => Lμ V T v d) (clockPoly T V d i)) 0)
    simpa [KnotMS] using hh
  exact
    Ready.linear (F := FieldEnd G d) he ((LinearMap.lsmul ℂ _ (cut (ψW P T) i j)).restrictScalars ℝ)

lemma truePace (d j : ℕ) : Ready (fun t : ℝ => coeff j (coupon (transit P T t) (uprightN P T d))) := by
  simp_rw [coupon, PowerSeries.coeff_mk, rules]
  refine accounts _ fun i hi => ?_
  let z := coeff i (uprightN P T d)
  let L : ℂ →ₗ[ℝ] FieldEnd G d := (LinearMap.toSpanSingleton ℂ _ z).restrictScalars ℝ
  suffices he : ∀ (j i : ℕ), Ready (fun v => coeff j (transit P T v ^ i)) by
    exact Ready.linear (F := FieldEnd G d) (he j i) L
  intro j i
  induction i generalizing j with
  | zero =>
    simp_rw [pow_zero]
    exact Ready.const _
  | succ i ih =>
    simp_rw [pow_succ, PowerSeries.coeff_mul]
    exact accounts _ (fun i _ => Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (ih _) (transit_coin ..))

lemma grade_flow {W : Initialize G} {Q : Prescription (Ensure.deck G)} (hG : G.Simple)
    (hp : Installed W T Q) (hq : Commuting Q) (d j : ℕ) :
    Ready (fun t : ℝ => coeff j (β_frame P T t d)) := by
  let L := Zx P T d
  let f (s : ℝ) := coupon (ψW P T) (KnotMS T V (-s) d)
  let g (s : ℝ) := coupon (transit P T s) (uprightN P T d)
  have hx (s) : β_frame P T s d = vault L * (f s * g s) := by
    rw [← cashComp P T s hG hp hq d, ← mul_assoc, (antidote (neutral P hG hp hq d)).2, one_mul]
  let X : FieldEnd G d →ₗ[ℝ] FieldEnd G d →ₗ[ℝ] FieldEnd G d := (Algebra.lmul ℝ _).toLinearMap
  have ht (j : ℕ) : Ready (fun s => coeff j (f s * g s)) := by
    simp_rw [PowerSeries.coeff_mul]
    exact
      accounts _ fun i _ =>
        Ready.pair (G := FieldEnd G d) X (ticket_align P T d i.1) (truePace P T d i.2)
  simp_rw [hx, PowerSeries.coeff_mul j]
  refine accounts _ fun i _ => ?_
  exact Ready.linear (F := FieldEnd G d) (ht i.2) (X (coeff i.1 (vault L)))
end Raha
end YM.WilsonMS.GFlow
