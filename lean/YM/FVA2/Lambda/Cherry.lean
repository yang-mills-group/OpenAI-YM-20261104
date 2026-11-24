import YM.FVA2.Lambda.SelectBV
/-!
# integrands part I WW. Scalar H & K arbitrary. Sum exact formulas with I normalization

 Direction may be arbitrary here; later project to gauge-marginal external pair. -/
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
open Slice (rib)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
variable (D E:ℝ→ℝ)(p q:QP)(k:G.ColorIndex)(K:ℂ)(c a b:Axis)(j:G.ColorIndex)
abbrev bone2 (u:ℝ→ℝ)(q:QP)(a b:Axis):ℂ:= ↑( u q.sq * precision a b q )
abbrev tail2 (u:ℝ→ℝ)(q:QP)(a:Axis):ℂ:= (↑( u q.sq * q.sq * q a ):ℂ)*I
def gum1 (q p:QP)(c a b:Axis):ℝ:= ∑ i:Axis,∑ l:Axis, precision i l (q+p) * rib i a c (-(q+p)) q p * rib l b c (-(q+p)) q p
def gum (q p:QP)(c:Axis) : ℝ:= ∑ a:Axis,∑ b:Axis, precision a b q * gum1 q p c a b
def syrup (q p:QP)(c:Axis): ℝ:= q.sq*(q+p).sq*q c*(q+p) c
def rind (j k:G.ColorIndex):ℂ:= ∑ l:G.ColorIndex, rune j l k^(2:ℕ)
local notation "g"=>triple G
abbrev men (a:Axis)(k:G.ColorIndex)(p:QP):Lane4 G:= (W₀ a k,p)
open Bead (attach)
lemma put_ξ (D:ℝ→ℝ)(F H:Law G)(i:BH G)(l r:List (Lane4 G)) (h:net l=p): Bead.attach D F H ((i,q)::l) r=∑ z:G.ColorIndex, let T(u v:BH G):= cross (parity v) (degree Ψ ((i,q)::l))*F ( (u,-(q+p))::(i,q)::l )*H ((v,q+p)::r); (∑ a:Axis,∑ b:Axis,bone2 D (-(q+p)) a b*T (W₀ a z) (W₀ b z))+(∑ a:Axis,tail2 D (-(q+p)) a*T (U₀ a z) (C₀ z))+(∑ a:Axis,tail2 D (-(q+p)) a*T (C₀ z) (U₀ a z)):= by
    rw [contact F H D (-(q+p)) _ _ (by simp only [net_cons,h]), paircol]; simp only [neg_neg]; -- maybe nested
lemma rib_flip : rib c a b (q+p) (-q) (-p)= -rib c a b (-(q+p)) q p:= by unfold Slice.rib; simp only [Pi.sub_apply, Pi.neg_apply, neg_neg]; ring
lemma gold : Bead.attach E g g [(W₀ a j,q), (W₀ c k,p)] [(W₀ b j,-q), (W₀ c k,-p)]= (E (q+p).sq:ℂ) * rind k j * gum1 q p c a b:= by
    rw [ put_ξ p q _ _ _ _ _ _ (by simp [net]) ]; -- args order?
    dsimp only; triples_core; unfold rind gum1; simp_rw [Finset.mul_sum, Finset.sum_mul]; push_cast; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _
    rw [rib_flip, ← r_clock k i j ]; simp only [Landau.sq_neg, Landau.k_even, Complex.ofReal_neg ]; linear_combination (norm:=ring) - (↑(E (q+p).sq):ℂ) * (precision v w (q+p):ℂ) * rune k i j^2 * (Slice.rib v a c (-(q+p)) q p:ℂ) * (Slice.rib w b c (-(q+p)) q p:ℂ) * Complex.I_sq
lemma amberU : Bead.attach E g g [(U₀ a j,q), (W₀ c k,p)] [(C₀ j,-q), (W₀ c k,-p)]= ( (↑(E (q+p).sq * (q+p).sq * (q+p) c * Slice.delta a c):ℂ) * I ) * rind k j := by
    rw [put_ξ p q _ _ _ _ _ _ (by simp [net]) ]; dsimp only; triples_core; unfold rind; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single c]; swap; · intro b _ hB; simp [Slice.delta, hB]
    swap; · simp
    rw [ show rune k j i= -rune k i j from (by rw [r_clock k j i, r_ortho j i k,← r_clock k i j]) ]; unfold tail2; simp only [Landau.sq_neg, Pi.neg_apply, show Slice.delta c c=1 from by simp [Slice.delta] ]; push_cast; ring
lemma amberC : Bead.attach E g g [(C₀ j,q), (W₀ c k,p)] [(U₀ a j,-q), (W₀ c k,-p)]= ( (↑(E (q+p).sq * (q+p).sq * (q+p) c * Slice.delta a c):ℂ) * I ) * rind k j := by
    rw [put_ξ p q _ _ _ _ _ _ (by simp [net]) ]; dsimp only; triples_core; unfold rind; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single c]; swap; · intro b _ hB; simp [Slice.delta, hB]
    swap; · simp
    rw [ show rune k j i= -rune k i j from (by rw [r_clock k j i, r_ortho j i k,← r_clock k i j]) ]; unfold tail2; simp only [Landau.sq_neg, Pi.neg_apply, show Slice.delta c c=1 from by simp [Slice.delta] ]; push_cast; ring
lemma sumRind (h:G.Simple): ( ∑ j,rind k j )=(G.casimir:ℂ):= by unfold rind; rw [Finset.sum_comm]; exact Slice.r_sq k h
lemma dive_G : (∑ a:Axis,∑ b:Axis, bone2 D q a b*((E (q+p).sq:ℂ) *rind k j *gum1 q p c a b)) = (↑(D q.sq * E (q+p).sq * gum q p c):ℂ)* rind k j:= by
    unfold bone2 gum; push_cast; simp_rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_ ; ring
lemma dive_A : ( ∑ a:Axis, tail2 D q a * ( ( (↑(E (q+p).sq * (q+p).sq*(q+p) c*Slice.delta a c):ℂ)*I) *rind k j ) )= -( (↑(D q.sq * E (q+p).sq * syrup q p c):ℂ)*rind k j ):= by
    rw [Finset.sum_eq_single c]; swap; · intro b _ h; simp [ Slice.delta, h ]
    swap; · simp
    rw [ show Slice.delta c c=1 from ( by simp [Slice.delta] ) ]; unfold syrup tail2; -- I2
    have he (a b:ℝ)(z:ℂ): ((a:ℂ)*I)*( (b:ℂ)*I*z)= -((↑(a*b):ℂ)*z):= by push_cast; linear_combination (a:ℂ) * (b:ℂ)* z* Complex.I_sq
    rw [he]; push_cast; ring
lemma jelly (h:G.Simple) : Area.first D E g g q [ ( W₀ c k,p ) ] [ ( W₀ c k,-p ) ]= ↑(G.casimir * D q.sq * E (q+p).sq * (gum q p c-2*syrup q p c)) := by
    unfold Area.first piece; rw [paircol]; triples_core; simp_rw [gold E p q k, amberU E p q k,amberC E p q k]; -- check simp works.Re
    simp_rw [dive_G D E p q k c, dive_A D E p q k c]; simp only [Finset.sum_add_distrib, ← Finset.mul_sum,Finset.sum_neg_distrib]; rw [sumRind k h]; push_cast; ring
end YM.FVA2.Lambda.Area
