import YM.FVA2.Lambda.Orchard
/-!
# Landau trace ∂ Ghost coupling needs no actual integration

 Reversal and transverse. Keep distinct p_S=0 and physical thickness t; pointwise statements. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- triples_core
noncomputable section
namespace YM.FVA2.Lambda.RoseS
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Canvas (quad high top_quad line4 triple upperquad trigger)
open Area
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{s t:ℝ}
local notation "g"=>triple G
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
variable (D E:ℝ→ℝ)(q:QP)(i j k l:G.ColorIndex)(a b:Axis)(w r:List (Lane4 G))(F:Law G)
lemma clogU : (∑ a:Axis, tail2 D q a*Bead.attach E g F [(U₀ a i,q),(C₀ j,0)] r )=0:= by
    obtain hp:= clogB D E q ( fun b:Axis=> ∑ x:G.ColorIndex,rune x j i*F ((W₀ b x,q)::r) ); simp only [mul_neg, Finset.sum_neg_distrib] at hp; simp_rw [ pawU ]; exact neg_eq_zero.mp hp
lemma shoots : Bead.attach E g g [( U₀ a i,q ), ( C₀ j,0 )] [( U₀ b k,-q ), ( C₀ l,0 )]= Bead.attach E g g [( U₀ b k,-q ),( C₀ l,0 )] [( U₀ a i,q ),( C₀ j,0 )]:= by
    rw [ Bead.opposite (r:=[(_,-q),_]) _ _ _ (by simp [net]) ( Bead.prudeT _ ) ( Bead.prudeT _ ) ]; -- check h infers? RHS unspecified
    triples_core -- ok
lemma clutter : ∑ a:Axis, tail2 D q a* quad G E g g [ (U₀ a i,q), (U₀ b j,-q),(C₀ k,0),(C₀ l,0) ]= 0:= by
    simp_rw [ Bead.expand4 E ( A:=(U₀ _ i,q) ) (B:=( U₀ b j,-q)) (Z:=(C₀ k,0)) (E:=(C₀ l,0)) ( by simp ) ( by simp ) ]; triples_core; simp_rw [ ← RoseS.shoots E q i l j k ]; simp only [mul_add, Finset.sum_add_distrib,mul_neg ]; -- adjust reorder
    simp_rw [ mul_left_comm _ (2:ℂ), Finset.sum_neg_distrib, ← Finset.mul_sum,clogU ]; simp
lemma excluded : Area.first D E g F q [(S₀ k,0)] r=∑ j:G.ColorIndex,∑ a:Axis,tail2 D q a * (∑ i:G.ColorIndex,∑ b:Axis, tail2 E (-q) b* (-(rune i j k) * F (( U₀ b i,q )::( U₀ a j,-q )::r ))) := by
    unfold Area.first piece; rw [paircol]; simp_rw [put_ξ (0:QP) q E g F _ [(S₀ k,0)] _ (by simp [net]) ]; triples_core; -- sign check expect K & jS internal orientation; adj fᵢⱼk times cross p_i=odd, degree left odd=>-. 
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
include hm
lemma ghost_T : ∑ a:Axis, tail2 D q a * high X 2 (s,t) [(U₀ a i,q), (U₀ b j,-q), (C₀ k,0), (C₀ l,0)] =0:= by
    have he a : fieldDim wfield [(U₀ a i,q), (U₀ b j,-q), (C₀ k,(0:QP)), (C₀ l,0)]=6:= rfl
    let w₀ (a:Axis): List (Lane4 G):= [( U₀ a i,q),(U₀ b j,-q),(C₀ k,0),(C₀ l,0)]; have hx(a:Axis): high X 2 (s,t) (w₀ a)=quad G (Shells.melt t) g g ( w₀ a ):= by rw [ upperquad hm (w₀ a) s t rfl (fun _=>by simp [w₀,net]), Canvas.not_marginal hm (w₀ a) s t rfl (by unfold w₀; rw [he]; decide), zero_add ]
    change ∑ a:Axis,tail2 D q a* high X 2 (s,t) (w₀ a)=0; simp_rw [hx]; exact clutter .. 
lemma respect : Area.first D E g (high X 2 (s,t)) q [(S₀ k,0)] [(C₀ i,0),(C₀ j,0)] =0:= by
    rw [excluded]; -- trans
    have h(a:Axis)(l w:G.ColorIndex) : (∑ b:Axis, tail2 E (-q) b * (-(rune l w k)* high X 2 (s,t) [( U₀ b l,q),(U₀ a w,-q),(C₀ i,0), (C₀ j,0)]))=0:= by
        simp only [ tailneg, neg_mul, mul_neg,neg_neg ]; have hr (b:Axis)(f:ℂ): tail2 E q b * (rune l w k*f)=rune l w k*(tail2 E q b*f):= by ring
        simp_rw [hr]; rw [ ← Finset.mul_sum, ghost_T E q l w i j a hm, mul_zero ]
    simp_rw [ h ]; simp
end YM.FVA2.Lambda.RoseS
