import YM.Integration.WilsonCapturedPrimaryAperture
import YM.Integration.WilsonCapturedPrimaryPaid

/-! Recover a positive-horizon filed coordinate on the genuine grouped density.
The only function sampled for physical values is the complete signed numerator
over the original rep's evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryOriginal
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPaid
open WilsonFirstReceivedRadialStencil
open scoped Classical ContDiff Topology

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

theorem registered {w : ℝ} (read : Readable A B R.p n w) (v : F.Coeff) :
    HasOrderAt (B.places v o) 1 d :=
  (((combination_bound R.p o read.paid v).1.smooth 1
    (one_healthy _ _ R.p.threshold_pos.le))).of_le (Nat.cast_le.mpr read.order)

def fieldFee (A : Hol G) (p : Probe G d) (D : ℕ) : ℝ :=
  probeFee A p + 3*WilsonCapturedPrimaryPolynomial.price D p.2.val

/-- The order controlling the rough field derivatives is the field horizon
plus one. All sample values can be bought after choosing the target power. -/
theorem original {w : ℝ} (read : Readable A B R.p n w) {q : Coefficient F n}
    (form : q.Format o A R) {κ s : ℝ} (paid : q.remBound o R κ s)
    (extra : d+1 ≤ R.p.order) {g C : ℝ} (hg : 0<g) (h1 : g≤1) (hc : 0≤C)
    (P v u : ℕ) (rent : s ≤ C/g^u) (p : Probe G d) (y : Polynomial ℂ)
    (D : ℕ) (degree : y.natDegree≤D) (rk : p.2.val≤D) :
    let Q := grade P d v
    let K := cutoff R.p g (Q+u)
    let r := radius R.p K
    let t := g^gap P v
    (∀ x∈B.footprint o, separation x o≤r) →
    R.p.threshold*(1+(r:ℝ))^2≤1 → 2*t≤1 →
    2*t*wallet A p r ≤ aperture G*R.p.threshold →
    WilsonCapturedPrimaryRough.price G (p.2.val+1) (wallet A p r)*
      (w*F.coeffSize (F.core q.x)+s) ≤ C/g^v →
    (∀ j≤D, ‖reading B R o q (ray A R.p o K p (t*node D j))-
      y.eval (((t*node D j:ℝ):ℂ))‖ ≤ C*g^Q) →
    ‖runProbe F p (projection F A R.p.threshold o q) -
      p.2.val.factorial*y.coeff p.2.val‖ ≤ fieldFee A p D*C*g^P := by
  intro Q K r t stencil geometry argument small gross values
  have ht : 0<t := pow_pos hg _
  let I := Ioo (-2*t) (2*t)
  let J := active o r
  let a := angular A R.p o r p
  have absx (x : ℝ) (hx : x∈I) : |x| < 2*t :=
    abs_lt.mpr ⟨by linarith only [hx.1],hx.2⟩
  have checked (x : ℝ) (hx : x∈I) :=
    chart A R.p o r p ((absx x hx).le.trans argument) geometry
      ((mul_le_mul_of_nonneg_right (absx x hx).le (zero_le_one.trans (wallet_one A p r))).trans small)
  have kcap : p.2.val+1≤d+1 := Nat.succ_le_succ (Nat.le_of_lt_succ p.2.isLt)
  obtain ⟨kf,kp⟩ := funded form paid K
  have pol (x : ℝ) : ContDiffAt ℝ (p.2.val+1) a x := by
    change ContDiffAt ℝ (p.2.val+1) (fun (z:ℝ) => ∑ j∈range (d+1), z^j • coeff A R.p o r p j) x
    exact ContDiffAt.sum (fun j _ => by fun_prop)
  have eqW : ray A R.p o K p = Planned.AtomRegular.bone (WilsonCapturedPrimaryRough.quadratic R.p) o J ∘ a :=
    funext fun x => physical A R.p o r p x
  have bill := WilsonCapturedPrimaryRough.original read kf kp (Nat.zero_lt_succ _)
    (kcap.trans extra) J a (wallet_one A p r) (I:=I) isOpen_Ioo isPreconnected_Ioo
    (fun x _ => pol x) (fun x hx i _ hi => derivatives A R.p o r p
      ((absx x hx).le.trans argument) i (hi.trans kcap)) (weights R.p o r geometry)
    (fun x hx => (checked x hx).2.1) (fun x hx => by
      change flags R.p.threshold ((Planned.AtomRegular.bone (WilsonCapturedPrimaryRough.quadratic R.p) o J ∘ a) x)=∅
      rw [←eqW]; exact (checked x hx).2.2)
  have daxil (x : ℝ) (hx : x∈Icc 0 t) : x∈I := ⟨by linarith only [ht,hx.1],by linarith only [ht,hx.2]⟩
  have tested := WilsonCapturedPrimaryPaid.probe read.sound form paid read.order read.power
    read.fit (registered read) hg h1 hc P v u rent p y D degree rk stencil
    (fun x hx => eqW ▸ (bill x (daxil x hx)).1)
    (fun x hx => by rw [eqW]; exact (bill x (daxil x hx)).2.trans gross)
    (fun j hj => (checked (t*node D j) (daxil _ ⟨mul_nonneg ht.le (node_mem hj).1,
      mul_le_of_le_one_right ht.le (node_mem hj).2⟩)).2.2) values
  exact tested.trans_eq (by unfold fieldFee;ring)

end YM.Integration.WilsonCapturedPrimaryOriginal
