import YM.MS.ScaleForest.Optics
import YM.Integration.FVA1Physical.Exchange.OriginalRoseRankNames

/-!
# The filed physical source: the quadratic negative chiral Rose

Use its literal lift. (There's no lift ambiguity at all for the curvature
index 0 Maxwell jet; the proof relies on that.) This is a physical label in
the unconverted exact-grade, `portDeck` conventions and not a stand-in such as the
single component `F₁₂²` mark.

The `z` in the notation for the fields of the `OpenAxis`/`JRad` optics is a
different argument from the dimensional parameter; name it `g` below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Quadratic
open Set Filter MeasureTheory Function Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Motif Literal Mach Halo Emit Local.Physical Land Theater
open FVA2.Position FVA2.Position.OpenAxis WilsonMS
open XSpace XSpace.Chiral XSpace.Normalize Lattice Maxwell Maxwell.Free
open scoped Topology ContDiff
variable {G : Gauge} {m n : ℕ}

/-- Curl tested on one axis pair. -/
def curlComponent (a b : Axis) (i : G.ColorIndex) : OpenAxis.Coord G 0 :=
  Prong b (basis a) i - Prong a (basis b) i

theorem curl_price (x : Labels.Taylor G 0) (a b : Axis) (i : G.ColorIndex) :
    curlComponent a b i x =(flavor 0 i (Maxwell.Free.cell a b)) (On.solve G 0 x) := by
  obtain ⟨V,rfl⟩ := (centring x).mpr (Theater.paid0 x)
  rw [On.on_shell]
  change _= V.val a b (fun _ : Fin 0 => 0) i
  rw [← match_leg V]
  let A := gaugeJet V
  change (Tensor.diagonal (A.val b) (basis a) i : ℝ) - Tensor.diagonal (A.val a) (basis b) i = _
  unfold Tensor.diagonal takeCurl
  simp only [Nat.cast_one, Nat.zero_add, one_smul, ContinuousMultilinearMap.curryLeft_apply,
    _root_.sub_apply, PiLp.sub_apply]
  have hr (a : Axis) : Fin.cons (basis a) (fun _ : Fin 0=> (0:E4))=(fun _ : Fin 1 => basis a) := by ext1 i; fin_cases i; simp
  rw [hr,hr]

theorem lift_letter (L : Maxwell.Probe G n) : On.lifting (symbol n L) =
    Theater.page n (asC G n (L.comp (On.solve G n))) := by
  apply Labels.eval_ext; intro A
  rw [On.lifted, Theater.bookX, Maxwell.symbol_test]; rfl

theorem lift_curl (a b : Axis) (i : G.ColorIndex) :
    On.lifting (symbol 0 (flavor 0 i (Maxwell.Free.cell a b))) = Theater.page 0 (asC G 0 (curlComponent a b i)) := by
  rw [lift_letter]
  exact congr_arg (fun x => Theater.page 0 (asC G 0 x)) (LinearMap.ext (fun x => (curl_price x ..).symm))

theorem basis_ray (g : ℂ) (a b : Axis) : OpenAxis.Ray G m 0 g b (basis a) =
    (2⁻¹:ℝ) • graft g a b (basis a) 0 := by simp [OpenAxis.Ray, slotDen, ite_smul]

theorem ramp_curl (a b : Axis) (i : G.ColorIndex) (g : ℂ) :
    seed G (On.lifting (symbol 0 (flavor 0 i (Maxwell.Free.cell a b)))) g m =
      cur g (chair m a) (chair m b) i := by
  rw [lift_curl,Vtheta, curlComponent,map_sub,map_sub]
  simp_rw [Pi.sub_apply, ramp_Jrad,basis_ray,graft_alt (a:=b) (b:=a)]
  change (2⁻¹:ℝ) • cur g (chair m a) (chair m b) i - (2⁻¹:ℝ) • - (cur g (chair m a) (chair m b) i) = _
  module

def oneColor (g : ℂ) (σ : Bool) (p : P) (i : G.ColorIndex) : Arts.Rack G m :=
  ∑ y : PlaqAxes, (↑(q σ p (six y) (endr y)) : ℂ) • cur g (chair m (six y)) (chair m (endr y)) i

theorem spark_sum (σ : Bool) (p : P) (c : G.ColorIndex) :
    spark σ (p,c) = ∑ y : PlaqAxes, (q σ p (six y) (endr y) : ℂ) •
      symbol 0 (flavor (G:=G) 0 c (Maxwell.Free.cell (six y) (endr y))) := by
  apply equalPol; intro A
  unfold Chiral.spark Chiral.arm Fq
  rw [Maxwell.symbol_test]
  simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply,symbol_test,
    Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul]

theorem spark_label (σ : Bool) (p : P) (c : G.ColorIndex) (g : ℂ) :
    seed G (On.lifting (spark σ (p,c))) g m = oneColor g σ p c := by
  rw [spark_sum]; simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,
    ramp_curl,oneColor]

/-- The lift of the actual quadratic arm (weights and slots recorded). -/
def roseLift (G : Gauge) : Theater.Film0 G 4 2 :=
  ⟨On.lifting ((Rose.tin G).val), by
    apply (Theater.cinema _).mpr
    have hh := Integration.FVA1Physical.Exchange.RoseNoise.original_rose_slot_degree (G:=G) 1
    let P := Rose.tin G
    have ht : MvPolynomial.IsWeightedHomogeneous bwt P.val (4,2) := hh
    have hv : reel 6 P = P := Rose.u_real
    refine ⟨?_, (On.fits P).2,?_⟩
    · exact ((Labels.pure_grade ..).mp (On.section_grade P ht))
    rw [← On.lift_conj]; exact congr_arg On.lifting (congr_arg Subtype.val hv)⟩

def roseMark (G : Gauge) (n : ℕ) := withSource (invoice _ _ _ (roseLift G)) (invoiceC (roseLift G)) n

theorem lifted_rose (G : Gauge) (m : ℕ) (g : ℂ) :
    Literal.value (Mob G) g (invoice _ _ _ (roseLift G)) m =
      (Rose.f^2 : ℝ) • ((2⁻¹:ℂ) • ∑ i : Name G,
        bite m G (oneColor g false i.1 i.2) (oneColor g false i.1 i.2)) := by
  rw [OpenAxis.priceR]
  change seed G (On.lifting ((Rose.f:ℂ)^2 • U G)) g m=_
  simp only [U,map_mul,map_sum,map_smul, Finset.smul_sum, Finset.sum_apply,Pi.smul_apply,
    seed_p]
  apply Finset.sum_congr rfl; intro (i,c) _
  rw [show minusV (i,c)=_ from (rfl: minusV (i,c) = spark false (i,c)), spark_label, ← Complex.ofReal_pow]; rfl

theorem bare_vertex (G : Gauge) (m : ℕ) :
    (roseMark G 0).symbol m = ((Rose.f:ℂ)^2) • ((2⁻¹:ℂ) • ∑ i : Name G,
      bite m G (oneColor 0 false i.1 i.2) (oneColor 0 false i.1 i.2)) := by
  rw [show (roseMark G 0).symbol = _ from Mach.onZero (invoice _ _ _ (roseLift G)), lifted_rose]
  rw [← Complex.ofReal_pow]
  rfl

end YM.MS.ScaleForest.Quadratic
