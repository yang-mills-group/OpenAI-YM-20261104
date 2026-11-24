import YM.RegulatorIR.Profiles.Village

/-!
# Aperture symbol expansion per-root, continuous-order ledger

Malm summation total Borel. Ink for *selected* finite apertures. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Labels Source Centered
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I:Type}{q u b p a i e k d m:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{J D:Choice M}
variable {S:Heir n G} (R: Reel S){T:S.Accounts}
section Basis
variable {P V:Portrait G}{X Y:Orders (Foot G)}
lemma basis_plus (h:Halo.BasisT a b P X)(H:Halo.BasisT a b V Y): Halo.BasisT a b (P+V) (X+Y):=by
 refine ⟨⟨h.origin.cap.add H.origin.cap,fun t f y=>congr_arg₂ (·+·) (h.origin.guise t f y) (H.origin.guise t f y),fun B L hv hs hp hc=> (h.origin.neat B L hv hs hp hc).add (H.origin.neat B L hv hs hp hc)⟩, fun i j=>?_, fun i j=>symmetric_add (h.symmetry i j) (H.symmetry i j),?_⟩
 · apply Set.Finite.subset ((h.canopy i j).union (H.canopy i j));intro z hz; by_cases hp:X i j z=0
   · right; intro hx; apply hz;change X i j z+Y i j z=0;rw [hp,hx];simp
   left; exact hp
 intro v; rw [show outing G (P+V) v=outing G P v+outing G V v from rfl,tale_add (Person.live h.origin v) (Person.live H.origin v), h.pose,H.pose,← mul_add];apply congr_arg;ext1 i; simp only [shelter,map_add,PowerSeries.coeff_mk]; unfold drums; rw [← Finset.sum_add_distrib]; apply sum_congr rfl;intro j _
 unfold strum; rw [← Summable.tsum_add (plaza (h.canopy i j) v) (plaza (H.canopy i j) v)]; apply tsum_congr;intro z; exact (add_mul ..).symm
where
 plaza {i:ℕ}{V: Packet (Foot G) i}(h:Prim.Bounded V)(v:Foot G→ℝ): Summable (fun y:Tuple (Foot G) i=> V y*noodle v y):=summable_of_hasFiniteSupport ((show (support V).Finite from h).subset (fun y hy=>left_ne_zero_of_mul hy))
lemma basis_scale (h:Halo.BasisT a b P X)(c:ℝ): Halo.BasisT a b (c • P) (c • X):=by
 refine ⟨⟨continuous_const.mul h.origin.cap,fun t f x=>congr_arg (c*·) (h.origin.guise t f x),fun B L hv hs hp hc=> contDiffAt_const.mul (h.origin.neat B L hv hs hp hc)⟩, fun i j=>?_,fun i j=>symmetric_scale (h.symmetry i j) _,?_⟩
 · exact (h.canopy i j).subset (fun y hy=>right_ne_zero_of_mul hy)
 intro x; rw [show outing G (c • P) x=(fun _:ℝ=>c)*outing G P x from rfl,tale_mul contDiffAt_const (Person.live h.origin x), tale_const,h.pose,mul_left_comm];apply congr_arg;ext1 i;rw [coeff_C_mul,shelter,shelter, coeff_mk,coeff_mk]; unfold drums; rw [Finset.mul_sum];apply sum_congr rfl;intro j _;exact (strum_tilt ..).symm
lemma ranks_scale {X:Type}{T: Orders X}(h:Ranks a T)(c:ℝ): Ranks a (c • T):=fun e r hr=> h e r (fun he=>hr (by change c • T e r=0;rw [he,smul_zero]))
lemma basis_total (s: Finset I)(P:I→ Portrait G)(T:I→ Orders (Foot G))(h:∀ i∈s,Halo.BasisT a b (P i) (T i))(hc:∀ i∈s,Ranks a (T i)): Halo.BasisT a b (∑ i∈s,P i) (∑ i∈s,T i) ∧ Ranks a (∑ i∈s,T i):=by
 induction s using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact ⟨⟨⟨continuous_const,fun _ _ _=>rfl,fun _ _ _ _ _ _=>contDiffAt_const⟩,fun _ _=> Set.finite_empty.subset (fun x h=> (h rfl).elim), fun _ _=>symmetric_zero,fun v=> by rw [show outing G 0 v=fun _=>0 from rfl, tale_const,map_zero]; rw [show shelter a (0:Orders (Foot G)) v=0 from ?_,mul_zero]; ext; simp [shelter,drums,strum]⟩, fun e i hi=> (hi rfl).elim⟩
 | insert i s he ih=>
    rw [sum_insert he,sum_insert he]; have hp:= ih (fun i hi=>h i (mem_insert_of_mem hi)) (fun i hi=> hc i (mem_insert_of_mem hi)); refine ⟨basis_plus (h i (mem_insert_self ..)) hp.1,fun v j hj=>?_⟩
    by_cases hg: T i v j=0
    · exact hp.2 v j (fun ht=>hj (by dsimp only [Pi.add_apply]; rw [hg,ht]; simp))
    exact hc i (mem_insert_self ..) v j hg
end Basis

namespace Aperture
variable {F:Labels.Frame G d}{θ:Hol G}(Z:SectionData F)(A:Z.Sound θ)(B:Bid.pop Z)(φ:PhaseTests d)(T:Tap F)(Q: Feeds)(ε:ℝ)(x:Room)

def planet (i:Stroke F)(z:Cover) := guardP (convey z (bare Z i.1)) (fees T Q i)
def framing (t:Cover)(i:Stroke F) := ε^4/ε^d * waveA i ε φ.phi (slide ε t-x)
include A B
lemma landed (i:Stroke F) (z:Cover): LocalStamp (planet Z T Q i z) d:=by
 have hx:= (authentically Z A B i.1).moves (t:=z);have hc:=hx.dresses (feesLive T Q i) (feesSmooth T Q i) (pays T Q i); rw [Nat.sub_add_cancel (WardBin.basis_degree _)] at hc;exact hc

def shape (i:Stroke F)(z:Cover): Orders (Foot G):= (stamp_symbol (landed Z A B T Q i z)).choose
def partV(z:Cover)(i:Stroke F):Orders (Foot G):= framing φ ε x z i • shape Z A B T Q i z -- order var x binder ordering needs test
lemma sign_v (i:Stroke F)(z:Cover): Halo.BasisT d d (flare φ T Z Q ε x z i) (partV Z A B φ T Q ε x z i):=by
 have he:=basis_scale (stamp_symbol (landed Z A B T Q i z)).choose_spec.1 (framing φ ε x z i);
 convert he using 1 <;>  try rfl
 ext1 t;ext1 y; exact mul_assoc ..
lemma sized_v (i:Stroke F)(z:Cover):Ranks d (partV Z A B φ T Q ε x z i):= ranks_scale (stamp_symbol (landed Z A B T Q i z)).choose_spec.2 _

def spineV : Orders (Foot G):= ∑ z∈Address.census ε φ.radius x, ∑ i:Stroke F,partV Z A B φ T Q ε x z i
lemma selling : Halo.BasisT d d (Testifies φ T Z Q ε x) (spineV Z A B φ T Q ε x) ∧ Ranks d (spineV Z A B φ T Q ε x):=by
 have hp(t:Cover): Halo.BasisT d d (Intag φ T Z Q ε x t) (∑ i:Stroke F,partV Z A B φ T Q ε x t i) ∧ _:=basis_total Finset.univ _ _ (fun i _=>sign_v Z A B φ T Q ε x i t) (fun i _=>sized_v Z A B φ T Q ε x i t)
 exact basis_total (Address.census ε φ.radius x) _ (fun z=> ∑ i:Stroke F,partV Z A B φ T Q ε x z i) (fun z _=>(hp z).1) (fun z _=>(hp z).2)
lemma spinC (hh:0<ε)(i k): Malm (fun x=> spineV Z A B φ T Q ε x i k):=by
 let f (x:Room)(z:Cover):= ∑ j:Stroke F,partV Z A B φ T Q ε x z j
 let C₀ (x:Room): Finset Cover:= Address.census ε φ.radius x
 have h(x z)(H:z∉C₀ x) : f x z=0:=by
    apply sum_eq_zero; intro j _; have he:waveA j ε φ.phi (slide ε z-x)=0:=by
       by_contra! ht; apply H; apply (Address.enroll _ hh _ _ _).mpr
       have hx:= φ.uses (in_ap j ε _ ht); change dist _ _ ≤ _ at hx; rwa [dist_eq_norm,sub_zero] at hx
    unfold partV framing; rw [he,mul_zero,zero_smul]
 intro y; have hp(x): ∑' z:Cover,f x z i k y=spineV Z A B φ T Q ε x i k y:=by rw [tsum_eq_sum (s:=C₀ x) (fun z hz=> by rw [h x z hz];rfl), spineV]; simp only [f,C₀,Finset.sum_apply]
 simp_rw [← hp]; apply Measurable.tsum; intro z; unfold f; simp_rw [Finset.sum_apply]; apply Finset.measurable_sum;intro j _; unfold partV
 exact ((continuous_const.mul ((slope_ap j ε φ.smooth).comp (continuous_const.sub continuous_id))).mul continuous_const).measurable
end Aperture
end YM.RegulatorIR.Profiles
