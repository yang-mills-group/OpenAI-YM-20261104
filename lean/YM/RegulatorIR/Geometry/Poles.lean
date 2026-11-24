import YM.RegulatorIR.Geometry.Edges
import YM.RegulatorIR.Uniform.Periodic
import Mathlib.Analysis.PSeries

/-!
Finite singular weights. Bound by integer shell counting at R/spacing (no
lg² loss). Use only when ℓ argument genuinely tracks output step lengths!
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Finset Function Lattice PertExtension Orb Gauge Budget Budget.Tuple Budget.Packet Motion Tariff Spatial Uniform ENNReal
open scoped ENNReal NNReal BigOperators Classical Topology
variable {n: Side} {l P R:ℝ}
lemma seats (hP:l*n.val=P)(hl:0<l)(x:OEdge n) : ‖seat l (position x)‖ ≤ P:=by
 have h (i : Site n): ‖slide l (Lattice.lift i)‖≤P/2:=by
    apply (pi_norm_le_iff_of_nonempty _).mpr; intro j
    simp only [slide_apply, Real.norm_eq_abs, abs_le]
    obtain ⟨h₁,h₂⟩:=lift_centers i j
    have ha : -(n.val:ℝ) ≤ (2:ℝ)*(Lattice.lift i j) := by exact_mod_cast h₁.le
    have hb : (2:ℝ)*(Lattice.lift i j) ≤ n.val:= by exact_mod_cast h₂
    constructor <;> nlinarith
 have hv i: ‖glint l i‖≤ l/2:=by
    rw [glint,norm_smul];apply (mul_le_mul_of_nonneg_left (show ‖slide l (step i)‖≤l from ?_) (norm_nonneg _)).trans_eq
    rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)];ring
    apply (pi_norm_le_iff_of_nonempty _).mpr;intro j; by_cases h':j=i
    · simp [h',abs_of_pos hl]
    simp [h',hl.le]
 have hx:l≤P:=hP ▸ le_mul_of_one_le_right hl.le (by exact_mod_cast n.property)
 apply (norm_add_le _ _).trans ((add_le_add (h x.val.1) (hv x.val.2)).trans (by linarith))

def polygon : Finset Cover:= Fintype.piFinset (fun _=>Icc (-4:ℤ) 4)
def plight (l:ℝ)(y: OEdge n):= seat l (position y)
def peak (P l:ℝ)(y : OEdge n):= nearest (P/2) (plight l y)
def altitude (P l:ℝ)(y:OEdge n):= singular P (plight l y)
lemma eastP (hP:l*n.val=P)(hl:0<l)(y:OEdge n): peak P l y∈ polygon := by
 have h:P>0:=hP ▸ mul_pos hl (by exact_mod_cast n.property)
 rw [polygon,Fintype.mem_piFinset]; intro i; rw [mem_Icc]; let A:= peak P l y
 have hv:dist (plight l y) (slide (P/2) A)≤ (P/2)/2:= by rw [dist_eq_norm]; exact halfwidth_le (P/2) (half_pos h) _
 have hQ: ‖slide (P/2) A‖≤2*P:=by
    have ht:= dist_triangle (slide (P/2) A) (plight l y) 0;rw [dist_comm (plight l y) _] at hv; rw [dist_zero_right,dist_zero_right] at ht; linarith [show ‖plight l y‖≤P from seats hP hl y]
 have hp : |P/2*(A i)| ≤ 2*P:= (norm_le_pi_norm (slide (P/2) A) i).trans hQ
 rw [abs_le] at hp
 constructor
 · exact_mod_cast (show (-4:ℝ) ≤ (A i:ℤ) from by nlinarith [hp.1])
 exact_mod_cast (show (A i:ℝ)≤4 from by nlinarith [hp.2])

def rim (l P R:ℝ)(x:OEdge n):ℕ:=⌊altitude P l x /R⌋₊
def band (l P R:ℝ)(w:Cover)(i:Axis)(j:ℕ) := Address.census l ((j+1:ℝ)*R) (slide (P/2) w-glint l i)
def ticketPole (l P R:ℝ)(p:Cover × Axis × ℕ) := Stalk (fun x:OEdge n=>(peak P l x,x.val.2,rim l P R x)) p
instance (l P R:ℝ) (p: Cover × Axis × ℕ): Fintype (ticketPole (n:=n) l P R p):=inferInstanceAs (Fintype (Stalk (fun x:OEdge n=>(peak P l x,x.val.2,rim l P R x)) p))
lemma count_rim (hl:0<l)(hR:0<R)(p : Cover × Axis × ℕ): ((Fintype.card (ticketPole (n:=n) l P R p)):ℝ≥0∞) ≤ ENNReal.ofReal ((1+2*((p.2.2+1:ℝ)*R) / l)^4):=by
 let f: ticketPole (n:=n) l P R p → (↑(band l P R p.1 p.2.1 p.2.2) : Set Cover) := fun y=> ⟨(position y.val).1,?_⟩
 have hf:Injective f:=by
    intro x y he; have h:Lattice.lift x.val.val.1=Lattice.lift y.val.val.1:=congr_arg Subtype.val he
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · rw [← wrap_lift x.val.val.1, h,wrap_lift]
    exact (show x.val.val.2=p.2.1 from congr_arg (fun q=> q.2.1) x.property).trans (congr_arg (fun q=> q.2.1) y.property.symm)
 apply le_trans _ (Address.total_enn l hl (mul_nonneg (by positivity) hR.le) (slide (P/2) p.1-glint l p.2.1))
 · apply Nat.cast_le.mpr; simpa [band] using (Fintype.card_le_of_injective f hf) -- simp band def
 have hx:= y.property
 rw [← show peak P l y.val=p.1 from congr_arg Prod.fst hx, ← show y.val.val.2=p.2.1 from congr_arg (fun q=> q.2.1) hx,← show rim l P R y.val=p.2.2 from congr_arg (fun q=> q.2.2) hx]; change (position _).1 ∈ band l P R (peak P l y.val) y.val.val.2 (rim l P R y.val)
 let X:=(position y.val).1; let i:= peak P l y.val; let j:= glint l y.val.val.2
 apply (Address.enroll _ hl _ _ _).mpr; rw [dist_eq_norm]; rw [show slide l X - (slide (P/2) i-j)=plight l y.val-slide (P/2) i from ?_]
 · exact ((div_lt_iff₀ hR).mp (Nat.lt_floor_add_one (altitude P l y.val/R))).le
 change slide l X- _= slide l X+ j- _; abel
end YM.RegulatorIR.Geometry
