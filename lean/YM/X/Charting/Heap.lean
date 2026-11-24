import YM.X.Charting.Viso
/-!
Integrated tail cut reaches continuum faster than epsilon powers after exact image equality. Uniform image Reg.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "K"=> (atTop:Filter ℕ)
variable {α β V:Type*}
variable (A:α→Beam q)(v:Beam q) (d:ℕ)(hd:0<d)(p : PlaqAxes)(a:Bool)
local notation "J" => Hair G

def heap (d:ℕ)(v:Beam q)(p:PlaqAxes)(a:Bool)(i:ℕ): Finset (Site (side q i)):= Finset.univ.filter fun x=> border q d i < minmass (v i) x p a
lemma heaps (i:ℕ): heap d v p true i ⊆ heap d v p false i:=fun x hx=> mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hx).2 (min_le_left ..)⟩
lemma minmass_pos (z: Site n)(w: Site n):0<minmass z w p a:= by cases a<;> simp [minmass,ticketN]
abbrev click (h:ℕ): ℝ:= (h:ℝ)⁻¹^6
lemma clicks (u w:Site n): click (minmass u w p a) ≤ click (ticketN u w)+click (ticketN u (second p w)):= by
   cases a
   · exact le_add_of_nonneg_right (by unfold click; positivity)
   by_cases h:ticketN u w ≤ ticketN u (second p w)
   · simp [minmass, min_eq_left h,click]
   simp [minmass, min_eq_right (le_of_not_ge h),click] -- edit?

lemma compared_sum (s:Finset (Site n))(f: Site n→ℝ) : ∑ x∈s,f (second p x)=∑ x∈s.image (second p), f x:= Eq.symm (Finset.sum_image (fun x _ y _ h=> (show Injective (second p (n:=n)) from Function.LeftInverse.injective (second₂ p)) h))  -- binder lambda? probably last applied x y autoImplicit

abbrev T :ℝ:= (2:ℝ)^5*3^4
def allowance (h:ℕ):ℝ:= T*(h:ℝ)⁻¹^ (6-4 :ℕ)
private lemma tail_bound (f:Finset (Site n))(o:Site n)(z:ℕ)(hz:z>0)(h:∀ x∈f, z≤ticketN o x): ∑ i∈f, click (ticketN o i)≤ allowance z:= by apply (Finset.sum_le_sum_of_subset_of_nonneg (s:=f) (t:= Finset.univ.filter fun i:Site n=> z≤ticketN o i) (fun x hx=>mem_filter.mpr ⟨mem_univ _,h _ hx⟩) (fun x _ _=> by positivity)).trans (tail (R:=n) o 6 hz (by norm_num)) -- order
lemma tariff (i:ℕ): ∑ x∈heap d v p a i, click (minmass (v i) x p a) ≤ 2*allowance (border q d i):= by
    let s:=heap d v p a i; have hc : 0≤ allowance (border q d i):=by unfold allowance T; positivity
    let Z (x:Site (side q i)):= click (ticketN (v i) x)
    have he :∑ x∈s,Z x≤allowance (border q d i):= tail_bound _ _ _ (border_pos ..) (fun x hx=> ((mem_filter.mp hx).2.trans_le (minmass₀ ..)).le)
    cases a with
    | false=> unfold s Z minmass at *; simp only [Bool.false_eq_true,↓reduceIte] at *; linarith
    | true=>
       refine (Finset.sum_le_sum (fun x (_:x∈s) => clicks p true (v i) x)).trans ?_; rw [Finset.sum_add_distrib, compared_sum p _ Z]; apply (add_le_add he (tail_bound _ _ _ (hz:=border_pos q d i) ?_)).trans_eq (_root_.two_mul ..).symm -- s = union
       intro y hy; obtain ⟨x,hx,rfl⟩:=mem_image.mp hy; exact le_trans (mem_filter.mp hx).2.le (min_le_right ..)

variable (P:poly (α × Hair G))
def summate (z:ℕ)(x:Site (side q z)) := fees (fun i=> A i z) (live a) P (vertex p) x
def separated (k : ℕ):ℂ:= ∑ x∈heap d v p a k, summate A p a P k x
include hq hd
lemma fit_high (H:∀ i:α, Capt d v (A i)): Ripe q (separated A v d p a P) (-((2*d:ℕ):ℤ)):= by
    obtain ⟨b,hb,H⟩:=whole hq d hd p a v A P H
    apply Ripe.eventual (B:= b*2*T)
    filter_upwards [H] with k hk; unfold separated; apply (norm_sum_le ..).trans; let s:=heap d v p a k; let f(x: Site (side q k)):= click (minmass (v k) x p a)
    calc
       _ ≤ ∑ x∈s,b*f x:= by
           refine Finset.sum_le_sum fun x hx=>?_; obtain hk:=hk x; simp_rw [moon,if_pos (mem_filter.mp hx).2] at hk
           unfold f click; rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (by exact_mod_cast minmass_pos p a (v k) x) _)]; rw [mul_comm]; exact hk
       _ = b*∑ x∈s,f x:= (Finset.mul_sum ..).symm
       _ ≤ _ := (mul_le_mul_of_nonneg_left (tariff v d p a k) hb.le).trans_eq (by rw [allowance,ticket_neg]; rw [cost_border,eps_eq]; simp only [show (6-4:ℕ)=2 from rfl]; rw [pow_mul' (magnify q k)⁻¹,inv_pow (magnify q k)];ring)
end YM.PositionX.Hinge
