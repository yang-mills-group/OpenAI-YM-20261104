import YM.FVA2.Lambda.Indigo
/-!
# Landau transversality for a left S or C tail of trc of n3

 `Area.first E D triple F` vanishes identically at p=0 external C
 even offshell. S,C,C contribution if F=high at n=2 to be handled after. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- triples_core
noncomputable section
namespace YM.FVA2.Lambda.Area
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Canvas (quad high top_quad line4 triple upperquad trigger)
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g"=>triple G
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
variable (D E:ℝ→ℝ)(p q:QP)(k l:G.ColorIndex)(c a b:Axis)(j i:G.ColorIndex)(F H: Law G) (r: List (Lane4 G))
lemma tailneg : tail2 D (-q) a= -(tail2 D q a):= by unfold tail2; simp [ Landau.sq_neg ]
lemma boneeven : bone2 D (-q) a b=bone2 D q a b:= by unfold bone2; rw [ Landau.sq_neg, Landau.k_even ]
lemma tailbone : ∑ a:Axis, tail2 D q a * bone2 E q a b=0:= by
    have he(a:Axis): tail2 D q a * bone2 E q a b=((↑(D q.sq*E q.sq*q.sq):ℂ)*I) *(↑( q a * precision a b q ):ℂ):= by unfold tail2 bone2; push_cast; ring
    simp_rw [he]; rw [← Finset.mul_sum, ← Complex.ofReal_sum, transit,Complex.ofReal_zero,mul_zero]
lemma pit (v:List (Lane4 G)): Bead.attach E g F [(C₀ j,q),(C₀ k,0)] v=0:= by
    rw [put_ξ 0 q _ _ _ _ _ _ (by simp [net])]; dsimp only; triples_core -- shape `C C`. internal W ghost no -> WW; internal U still ghost +1. 
lemma pawW (v:List (Lane4 G)): Bead.attach E g F [( W₀ a j,q),(C₀ k,0)] v = tail2 E q a* ( ∑ i:G.ColorIndex,rune j k i * F ( (C₀ i,q)::v )):= by
    rw [put_ξ 0 q _ _ _ _ _ _ (by simp [net]), Finset.mul_sum ]; dsimp only; triples_core; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_eq_single a]; swap; · intro b _ hb; simp [ Slice.delta, hb ]
    swap; · simp
    rw [show Slice.delta a a=1 from ( by simp [Slice.delta] ), tailneg]; push_cast; ring
lemma pawU(v:List (Lane4 G)) : Bead.attach E g F [(U₀ a j,q), (C₀ k,0)] v = ∑ b:Axis,bone2 E q a b*(∑ i:G.ColorIndex,rune i k j * F ( (W₀ b i,q)::v )):= by
    rw [put_ξ 0 q _ _ _ _ _ _ (by simp [net])]; dsimp only; triples_core; rw [ Finset.sum_comm ]; -- order? left i color,a internal; b inner; want sum_b; easiest collapse a first
    rw [ Finset.sum_eq_single a ]; swap; · intro b _ h; simp [Slice.delta, Ne.symm h]
    swap; · simp
    rw [ Finset.sum_comm ]; simp only [show Slice.delta a a=1 from by simp [Slice.delta], Complex.ofReal_one, mul_one, boneeven, Finset.mul_sum ]
lemma clogA (f:Axis→ℂ): (∑ a:Axis,∑ b:Axis,bone2 D q a b*( tail2 E q a * f b ))=0:= by
    rw [ Finset.sum_comm ]; apply Finset.sum_eq_zero; intro b _; have hz(a:Axis): bone2 D q a b*(tail2 E q a*f b)=tail2 E q a*bone2 D q a b*f b:= by ring
    simp_rw [hz,← Finset.sum_mul,tailbone,zero_mul]
lemma clogB (f:Axis→ℂ): (∑ a:Axis,tail2 D q a * (-(∑ b:Axis,bone2 E q a b*f b)))=0:= by simp_rw [ mul_neg, Finset.sum_neg_distrib,Finset.mul_sum ]; rw [ Finset.sum_comm ]; apply neg_eq_zero.mpr; apply Finset.sum_eq_zero; intro b _; simp_rw [← mul_assoc,← Finset.sum_mul, tailbone, zero_mul ]
lemma worm_C : Area.first D E g F q [(C₀ k,0)] r=0:= by
    unfold Area.first piece; rw [paircol]; triples_core; simp_rw [pit E q k _ F,pawU E q k _ _ F,pawW E q k _ _ F, clogA,clogB ]; simp
end YM.FVA2.Lambda.Area
