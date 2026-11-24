import YM.FVA2.Position.OrbitPole
/-!
# Covariance of the concrete D regulator solutions as simultaneous poles

Comet relative to bulk. We don't need claim any uniqueness on disconnected common
vacuum channel separately. Here treat covariance for pole-computation purposes. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Park
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Heat
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl
open _root_.YM.MS.Shine Brass MS.Color Garment.Wave Garment.Wick Signal Book.Convolve-- Signal ambig
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n k:ℕ}{G:Gauge} (s t:Signed) {r q:ℤ}
variable {X Y F: Flats G}{f:Coat G}{U:Rip G}
local notation "Ω"=> hoop s
local notation "V"=> flats_t s
local notation "Φ"=> coat_t s
lemma contrive {b:Bool}(A B:Mob G)(h:Knot true U)(hp:closedF U b): Ω (arbor U A B)=arbor U (Ω A) (Ω B):= by funext m; exact Pilot.Transport.gatherR (h.token.turn m (Brass.viewD s m) (fun i=> Bool.noConfusion i)) (A m) (B m) (hp m) (hp m)
lemma anchor {b:Bool}(h:Knot true U)(hp:closedF U b)(i j:Coat G): Φ (tapeB (squad U) i j)=tapeB (squad U) (Φ i) (Φ j):= funext fun z=> contrive s (i z) (j z) h hp
lemma zap (i j:Coat G)(a b:ℕ): TreeN U (Finsupp.single a i) (Finsupp.single b j)= Finsupp.single (b+a) (tapeB (squad U) i j):= by
 unfold TreeN; rw [ explode, Finsupp.lsum_single ]; exact blast_sl ..
lemma travelN {b:Bool}(h:Knot true U)(hp:closedF U b)(X Y:Flats G): V (TreeN U X Y)= TreeN U (V X) (V Y):= by
 induction X using Finsupp.induction_linear with
 | zero=> simp
 | add i j hi hj=> simp only [map_add,LinearMap.add_apply,hi,hj]
 | single a i=>
    induction Y using Finsupp.induction_linear with
    | zero=> simp
    | add l r hl hr=> simp only [map_add,hl,hr]
    | single j y=> rw [zap,flats_zk,flats_zk,flats_zk,zap,anchor s h hp] -- see ordem
lemma endemic (h:Sun false f)(hp: Knot true U): Spotty (Φ ( swamp U f )) ( swamp U (Φ f)) := by
    filter_upwards [sunny h, high0] with i hi hI; rw [coat_x, swamp_spec hp.clearer hi hI, swamp_spec hp.clearer (flows s hi) hI, map_smul, floorS s hp hi i hI]; rfl
lemma quotaH (h: Moony false X)(hp:Knot true U): Pact (V (CycleN U X)) (CycleN U (V X)):= by
 intro i; rw [flats_x]; cases i with| zero=> rw [CycleN,bland (by omega),bland (by omega),map_zero] | succ i=> unfold CycleN; rw [blade, blade, flats_x]; exact endemic s (h i) hp
lemma exists_head (h:Gang true n r X): Pact (V X) X:= by
 obtain ⟨m,hm⟩:= h.price; intro i; filter_upwards [sunny ( hm i |>.fine.tune )] with j hj; rw [ flats_x, coat_x ]; exact funext fun _=> hj.token.turn _ ( viewD s _ ) (fun h=>Bool.noConfusion h)
variable {B:T (Flats G)}
lemma masterN (h:∀ i, Gang true 4 0 (B i))(X:T ( Flats G )) (n:ℕ): Pact (V ( platform B n X )) (platform B n (V ∘ X)):= by
    unfold platform; rw [map_sum]; refine pact_sum _ (fun i hi=>?_ ); rw [ drive0,travelN s (A_caps G 0) (cl_a G 0) ]; exact pair_pact _ (exists_head s (h i.1)) (fun _=>EventuallyEq.rfl)
variable {P Q a:T ( Coat G )}{X:T (Flats G )}{M:ℕ}
-- beam covariance, maintaining selected Pole as all values (not just fourD limit).
theorem soaring (he:comet M r B a X P)(hX:∀ i, Gang true 4 0 ( B i)): comet M r B (Φ ∘ a) (V ∘ X) (Φ ∘ P):= by
    intro i; obtain ⟨⟨R,Ht,H,Hq⟩,-⟩:= he i; refine ⟨ ⟨ R, Joint.via ( Direct s Ht ) ?_, clash s H, Cw s Hq ⟩, False.elim ⟩; rw [map_add]; exact common ( masterN s hX X i ) (quotaH s (clockMoon H) (A_caps G 0))
lemma strongest (he:leader G B a P)(k): Gang true 4 0 ( B k ):= gang ( he k ) -- κ witness

end YM.FVA2.Position.Park
