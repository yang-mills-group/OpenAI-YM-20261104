import YM.LocalTaylorR2.Snapshot
import YM.LocalTaylorR2.Tree

/-!
# Local cumulant price. Charge each log, not an estimate of the (volume-dependent)
 evaluated exponential. Leases paid once per each COPY of an inherited E
 or loop term, not washing them out in global Taylor weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves RG01.Survive
variable {j k n l : ℕ} {v r d A D x C' θ ζ c' ρ:ℝ} {U:Molecule S} {χ : Chi}
namespace Tender
variable (Ξ:Utopia H j v d r C' χ) (hB: LocalBookingsR2 ζ c' Ξ)
variable (h:1≤betaF G s L)(hζ:0≤ζ)
variable (hθ:1≤θ)
def forge (θ:ℝ) (q:Paint U l) := ∏ i: ↥(logs U), θ * (Ξ.goalsL i.val)^Series.rank (q i)
abbrev massb (Q: YM.ConnectedActivityE6.Target G P) (L:Side) (μ s:ℝ) (θ:ℝ) (ρ:ℝ) (l:ℕ) (b:ℝ) := current Q L μ s + ((l+1:ℝ)*θ*ρ)*b
abbrev perLog (L:Side)(ζ s:ℝ) (i:LogIndex c f):= betaF G s L^leaseLog ζ c f i
def extraFee (L:Side) (ζ s:ℝ) (q:Paint U l) := ∏ i: ↥(logs U), perLog (G:=G) L ζ s i.val ^Series.rank (q i)

lemma logN (i:LogIndex c f):0≤Ξ.goalsL i:= Ξ.uses.nonneg (.inr (.inl i))
include hθ
lemma forgeN (p:Paint U l):0≤forge Ξ θ p:=Finset.prod_nonneg fun _ _=> mul_nonneg (zero_le_one.trans hθ) (pow_nonneg (logN ..) _)
omit hθ
include h hζ
lemma logHigh (i:LogIndex c f): 1≤ perLog (G:=G) L ζ s i:= Real.one_le_rpow h (leaseNN hζ (.inr (.inl i)))
lemma high (p:Paint U l):1≤extraFee (G:=G) L ζ s p := by unfold extraFee; exact Finset.one_le_prod fun _ _=>one_le_pow₀ (logHigh h hζ _)
include hB
omit h hζ in
lemma rim (i:LogIndex c f): perLog (G:=G) L ζ s i* Ξ.goalsL i≤c':=by
  have hp:= hB.leases.atom (by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]) Q.usable.le (.inr (.inl i)) (exChart ..)
  exact hp
lemma slack (hb:c'≤1) : ∀ i,Ξ.goalsL i≤1:=fun i=> (le_mul_of_one_le_left (logN _ _) (logHigh h hζ i)).trans ((rim Ξ hB i).trans hb)
include hθ
lemma rated (U:Molecule S) (hp:Pure U) (he:1≤ρ) (hm: ρ*c' ≤ 1) :
    (∑ q:Paint U l, forge Ξ θ q*ρ^(inserts q)*extraFee (G:=G) (L:=L) ζ s q) ≤ ∏ i∈U, entry Ξ ((l+1:ℝ)*θ*ρ) ζ i := by
  let g (i:↥(logs U)) (q:Series.Letter l) := θ * (ρ*(perLog (G:=G) L ζ s i.val*Ξ.goalsL i.val))^Series.rank q
  have hg (i:↥(logs U)) (q:Series.Letter l):0≤g i q:= mul_nonneg (zero_le_one.trans hθ) (pow_nonneg (mul_nonneg (zero_le_one.trans he) (mul_nonneg (zero_le_one.trans (logHigh h hζ _)) (logN _ _))) _)
  have hv (q:Paint U l): forge Ξ θ q*ρ^(inserts q)*extraFee (G:=G) (L:=L) ζ s q=∏ i,g i (q i):=by
    unfold forge extraFee inserts; rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]; exact prod_congr rfl (fun i _=> by unfold g; rw [mul_pow, mul_pow]; ring)
  let v:=entry Ξ ((l+1:ℝ)*θ*ρ) ζ
  have hx i : v (identityLog i)=((l+1:ℝ)*θ*ρ)*(perLog (G:=G) L ζ s i*Ξ.goalsL i):= entryO Ξ ((l+1:ℝ)*θ*ρ) ζ (.inr (.inl i))
  have hd: (∏ i∈U,v i)= ∏ i: ↥(logs U), v (identityLog i.val):= by
    conv_lhs=> arg 1; rw [allPure hp]
    rw [prod_image (fun _ _ _ _ h=> scenic_inj h), ← prod_attach (logs U)]; rfl
  change _ ≤ ∏ i∈U,v i; rw [hd]; simp_rw [hv]; rw [← Fintype.prod_sum]; refine Finset.prod_le_prod (fun i _=> Finset.sum_nonneg (fun j _=>hg i j)) ?_
  intro i hi
  apply le_trans (Finset.sum_le_sum (fun q (_:q∈(univ:Finset (Series.Letter l))) => mul_le_mul_of_nonneg_left (pow_le_of_le_one (show 0≤ρ*(perLog (G:=G) L ζ s i.val*Ξ.goalsL i.val) from mul_nonneg (zero_le_one.trans he) (mul_nonneg (zero_le_one.trans (logHigh h hζ _)) (logN _ _))) ((mul_le_mul_of_nonneg_left (rim _ hB i.val) (zero_le_one.trans he)).trans hm) (by exact Nat.succ_ne_zero (q:ℕ))) (zero_le_one.trans hθ)))
  rw [hx]; simp only [sum_const,nsmul_eq_mul,card_univ]; rw [show Fintype.card (Series.Letter l)=l+1 from Fintype.card_fin _]; apply le_of_eq; push_cast; ring
-- specialize without billing leases (expose both)
lemma inflated (U:Molecule S) (hp:Pure U) (he:1≤ρ) (hm:ρ*c'≤1) :
    (∑ q:Paint U l,forge Ξ θ q * ρ^inserts q) ≤ ∏ i∈U,entry Ξ ((l+1:ℝ)*θ*ρ) ζ i := by
  apply (rated Ξ hB h hζ hθ U hp he hm).trans' (Finset.sum_le_sum ?_)
  intro i _; exact le_mul_of_one_le_right (mul_nonneg (forgeN Ξ hθ i) (pow_nonneg (zero_le_one.trans he) _)) (high h hζ _)
end Tender
end YM.LocalTaylorR2
