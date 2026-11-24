import YM.Integration.WilsonCoverKineticMoment
import YM.Integration.WilsonConditionalTaylorFiniteHessian
import YM.Integration.WilsonConditionalTaylorKineticWrap
import YM.Integration.WilsonMovingRunWickCoordinates

/-! Normalize the full finite kinetic Hessian on the original observing
tori. The quadratic weight, factor two, physical period and finite
denominator remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRunKineticPeriodIncome
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Midpoint
open WilsonMovingPolynomialPull RGComparison.Core16
open scoped Classical BigOperators Topology

private theorem translated {n : Side} {I : Type} (T : Tile (Tor n I) 2) (c : I)
    (up : Up T) (sym : Agate T) (a b : Site n) :
    T ![(a,c),(b,c)] = T ![(b-a,c),(0,c)] := by
  let v : chain (Tor n I) 2 := ![(b,c),(a,c)]
  have swap : v ∘ Equiv.swap (0:Fin 2) 1 = ![(a,c),(b,c)] := by
    funext k; fin_cases k <;> simp [v]
  have shift : Lotus.tint (-a) ∘ v = ![(b-a,c),(0,c)] := by
    funext k; fin_cases k <;> simp [v,Lotus.tint,sub_eq_add_neg]
  rw [← swap,sym v,← shift,up]

theorem average {n : Side} {I : Type} (T : Tile (Tor n I) 2) (c : I)
    (up : Up T) (sym : Agate T) (φ : Site n→ℝ) :
    (Fintype.card (Site n):ℝ)⁻¹ * (∑ a : Site n, ∑ b : Site n,
      (2*T ![(a,c),(b,c)])*φ (b-a)) =
      2*(∑ v : Site n,T ![(v,c),(0,c)]*φ v) := by
  let f := fun v : Site n => T ![(v,c),(0,c)]*φ v
  have linear (a:Site n) : (∑ b : Site n,(2*T ![(a,c),(b,c)])*φ (b-a)) =
      2*(∑v,f v) := by
    simp_rw [translated T c up sym a,mul_assoc]
    rw [← Finset.mul_sum]
    apply congrArg (fun v:ℝ=>2*v)
    simpa only [sub_eq_add_neg,Equiv.coe_addRight,f] using Equiv.sum_comp (Equiv.addRight (-a)) f
  simp_rw [linear]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀,one_mul]
  exact_mod_cast (Fintype.card_pos (α:=Site n)).ne'

theorem measured {G : Gauge} {n : Side} (p : Pap (wire G n)) (e : ℕ) (c : G.ColorIndex) (h : Civic p) :
    caliper n (Lis.sun G c) (coeff e (place (WilsonMovingGaussianCoordinates.link G n).symm p)) =
    2*(∑ x : Site n,rancho p e 2 ![(x,coord (1:Axis),c),(0,coord (1:Axis),c)] *
      (Cork.ch 0 (lift x)*Cork.ch 0 (lift x))) := by
  let E := WilsonMovingGaussianCoordinates.link G n
  have pair (a b : Site n) :
      marble 2 (coeff e (place E.symm p)) ![Wave.primary (a,(1:Axis)) c,Wave.primary (b,(1:Axis)) c] =
      rancho p e 2 ![(a,coord (1:Axis),c),(b,coord (1:Axis),c)] := by
    change marble 2 (MvPolynomial.rename E.symm (coeff e p)) _=_
    rw [Shore.pebble,Shore.cores_once]
    change marble 2 (coeff e p) (E ∘ _) = _
    apply congrArg (marble 2 (PowerSeries.coeff e p))
    funext k; fin_cases k <;> rfl
  rw [WilsonConditionalTaylorFiniteHessian.moment]
  change _*(∑a : Site n,∑b : Site n,(2*marble 2 (coeff e (place E.symm p)) _)*_) = _
  simp_rw [pair,pow_two]
  exact average (rancho p e 2) (coord (1:Axis),c) (civic_up n p h e 2)
    (marble_agate 2 (PowerSeries.coeff e p)) (fun x : Site n=>Cork.ch 0 (lift x)*Cork.ch 0 (lift x))

variable {G : Gauge} (R : Run G) (roofs : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G)

def finite (N i e : ℕ) (tags : ∀n,(primary (destination R.family.path.levels N i).patch
    R.family.path.levels.clock.kernel n).Choices) (n : Side) :=
  let V := R.family.path.levels
  let P := destination V N i
  let b := fun k=>(V.blocks k 0).branches
  let W := Dove.model V roofs b R.metals.O a N (i+1)
  caliper n (Lis.sun G a) (coeff e (place (WilsonMovingGaussianCoordinates.link G n).symm
    (Bank.burn P (roofs i) W R.metals.O (b i) tags n)))

theorem numerator (simple : G.Simple) (N i : ℕ) (hi : i<N) (e : ℕ)
    (tags : ∀n,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices) :
    let V := R.family.path.levels
    let P := destination V N i
    let b := fun k=>(V.blocks k 0).branches
    let W := Dove.model V roofs b R.metals.O a N (i+1)
    Tendsto (fun per : ℕ=>finite R roofs a N i e tags (R.family.side i per))
      atTop (𝓝 (2*coeff e (Roof.epoch a P (roofs i) V.clock.kernel W R.metals.O (b i)))) := by
  intro V P b W
  have booked := (Dove.genu V roofs b R.metals.O a R.alloy.B.ratio simple (i:=i+1) (N:=N) hi).toStory
  have bought := WilsonCoverKineticMoment.original R roofs a simple N i hi e tags
  have incidence (n : Side) := Bank.emperor P (roofs i) W R.metals.O (b i) booked (V.clock.adm i) R.alloy.B.ratio tags n
  have growth : Tendsto (fun per:ℕ=>(R.family.side i per).val) atTop atTop :=
    (show StrictMono (fun per:ℕ=>(R.family.side i per).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator i).pos).tendsto_atTop
  have held : Tendsto (R.family.side i) atTop atTop := tendsto_atTop.2 fun n=>growth.eventually_ge_atTop n.val
  apply ((tendsto_const_nhds (x:=(2:ℝ))).mul bought).comp held |>.congr'
  exact Filter.Eventually.of_forall fun per=>(measured _ e a (incidence (R.family.side i per))).symm

end YM.Integration.WilsonRunKineticPeriodIncome
end
