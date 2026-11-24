import YM.FVA2.Lambda.Cherry
/-!
# Integral numerators d=4 part II for C/U

 Includes transversality algebra for arbitrary FP projects. Need at chosen p=t*e_c only. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- triples_core
noncomputable section
namespace YM.FVA2.Lambda.Area
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect MS.Landau.Detect.Mark
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Canvas (quad high top_quad line4 triple upperquad trigger)
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g"=>triple G
variable (D E:ℝ→ℝ)(p q:QP)(k:G.ColorIndex)(c a b:Axis)(j:G.ColorIndex)
lemma rose : Bead.attach E g g [(C₀ j,q),(C₀ k,p)] [(U₀ a j,-q),(U₀ c k,-p)] =0:= by rw [put_ξ p q _ _ _ _ _ _ (by simp [net])]; dsimp only; triples_core
lemma hollowU : Bead.attach E g g [(U₀ a j,q),(C₀ k,p)] [(C₀ j,-q),(U₀ c k,-p)]= bone2 E (q+p) a c *rind k j:= by
    rw [put_ξ p q _ _ _ _ _ _ (by simp [net])]; dsimp only; triples_core; unfold rind; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    -- collapse δ. K sign -? internal ∧ zero
    rw [Finset.sum_eq_single a]; swap; · intro b _ hb; simp [Slice.delta, Ne.symm hb,hb]
    swap; · simp
    rw [ Finset.sum_eq_single c ]; swap; · intro b _ hb; simp [Slice.delta,Ne.symm hb,hb]
    swap; · simp
    -- sign, cast
    rw [r_ortho i k j, ← r_clock k i j ]; rw [bone2, k_even,sq_neg]; simp [Slice.delta,bone2]; ring_nf; simp
lemma houseW : Bead.attach E g g [(W₀ a j,q), (C₀ k,p)] [(W₀ b j,-q), (U₀ c k,-p)] = ( (Slice.delta c b:ℂ) * tail2 E (q+p) a ) * rind k j:= by
    rw [put_ξ p q _ _ _ _ _ _ (by simp [net])]; dsimp only; triples_core; unfold rind; rw [ Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _
    rw [ Finset.sum_eq_single a ]; swap; · intro b _ hb; simp [Slice.delta, Ne.symm hb,hb]
    swap; · simp
    rw [r_clock j k i, r_ortho j i k,←r_clock k i j ]; rw [show Slice.delta a a=1 from ( by simp [Slice.delta] ) ]; unfold tail2; rw [Landau.sq_neg (q+p), Pi.neg_apply]; push_cast; ring
lemma transit : ∑ a:Axis,q a * precision a b q=0:= by
    unfold precision Landau.delta; simp_rw [mul_sub,Finset.sum_sub_distrib,mul_ite]; simp; unfold Momentum.sq; rw [Finset.mul_sum]; exact sub_eq_zero.mpr ( Finset.sum_congr rfl ( fun i _=> by ring ) )
variable (t:ℝ)
abbrev rayC (c:Axis)(t:ℝ): QP:= t • spray c
abbrev surf (q:QP)(c:Axis):ℝ:= Landau.precision c c q
lemma sip_t : (∑ a:Axis, q a* precision a c (q+rayC c t)) = - t * surf (q+rayC c t) c := by
    obtain he:= transit (q+rayC c t) c; simp only [Pi.add_apply,add_mul, Finset.sum_add_distrib] at he; rw [add_eq_zero_iff_eq_neg] at he; rw [he]; unfold rayC spray; simp [Pi.single_apply,mul_ite,ite_mul]
lemma sip_h : (∑ a:Axis, (q+rayC c t) a* precision a c q) = t * surf q c:= by
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,transit,zero_add, rayC,spray]; simp [Pi.single_apply,mul_ite,ite_mul]
lemma axis_surf : surf (q+rayC c t) c=surf q c:= by
    unfold surf; simp [Landau.precision, Landau.delta, rayC,spray,Momentum.sq, Pi.single_apply,ite_pow, add_pow_two, mul_ite, Finset.sum_add_distrib]; ring
local notation "p☆" => rayC c t
def van (q p:QP)(c:Axis):ℝ:= surf q c * (q.sq + (q+p).sq)
lemma slip_U : (∑ a:Axis, tail2 D q a * (-( bone2 E (q+p☆) a c * rind k j)))= (↑(D q.sq * E (q+p☆).sq * t * q.sq * surf q c):ℂ)*I*rind k j:= by
    have hx (a:Axis): tail2 D q a * (-( bone2 E (q+p☆) a c * rind k j))= ((↑( -(D q.sq * E (q+p☆).sq * q.sq)):ℂ)*I*rind k j ) * (↑(q a * precision a c ( q+p☆ )):ℂ):= by unfold tail2 bone2; push_cast; ring
    simp_rw [hx]; rw [← Finset.mul_sum, ← Complex.ofReal_sum, sip_t, axis_surf ]; push_cast; ring
lemma slip_W : (∑ a:Axis,∑ b:Axis, bone2 D q a b *(( (Slice.delta c b:ℂ) * tail2 E (q+p☆) a ) * rind k j) )= (↑(D q.sq * E (q+p☆).sq * t * (q+p☆).sq *surf q c):ℂ)*I*rind k j:= by
    have hx(a:Axis): (∑ b:Axis, bone2 D q a b *(( (Slice.delta c b:ℂ) * tail2 E (q+p☆) a ) * rind k j) )= ((↑( D q.sq * E (q+p☆).sq * (q+p☆).sq ):ℂ)*I*rind k j) * (↑( (q+p☆) a * precision a c q):ℂ):= by
        rw [Finset.sum_eq_single c]; swap; · intro b _ hb; simp [Slice.delta, Ne.symm hb];
        swap; · simp
        rw [ show Slice.delta c c=1 from by simp [Slice.delta] ]; unfold bone2 tail2; push_cast; ring
    simp_rw [hx]; rw [← Finset.mul_sum, ← Complex.ofReal_sum, sip_h ]; push_cast; ring
lemma bust (h:G.Simple): Area.first D E g g q [ (C₀ k,p☆ ) ] [ (U₀ c k,-p☆) ]= (↑(G.casimir * D q.sq * E (q+p☆).sq * t* van q p☆ c):ℂ)*I:= by
    unfold Area.first piece; rw [ paircol ]; triples_core; simp_rw [houseW E p☆ q k, hollowU E p☆ q k, rose E p☆ q k c ]; simp only [neg_zero,mul_zero,Finset.sum_const_zero, add_zero]; simp_rw [slip_U D E q k c _ t, slip_W D E q k c _ t ]; simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; rw [sumRind k h]; unfold van; push_cast; ring
end YM.FVA2.Lambda.Area
