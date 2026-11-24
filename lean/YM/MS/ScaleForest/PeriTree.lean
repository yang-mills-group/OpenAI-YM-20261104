import YM.MS.ScaleForest.Perimeter
import YM.MS.ScaleForest.Beamline
/-!
# Top of the contracted tree

On the current radius, not IR limit or scaleless. Compute how the pole vertex
acts, for use in the scale-ordered evaluation. Project it on rank-two A,
because the exterior lines in this contribution are all gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {m:ℕ} (μ:ℝ) {K : Rip G} {W: Mob G} (p q : SectorP m)
   (g:G.Simple)
local notation "R" G=> ghostR G
local notation "Q" => cursor false

abbrev Cur (X:Pupil)(i:Name G)(p:SectorP m)(l:Shaft G m):ℂ:= antenna X i l.2 l.1 p
lemma antenna_right (X:Pupil)(i:Name G): stableA p (Cur X i p) := by
    intro a; unfold Cur antenna; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun j _=>?_ ; unfold rampLeg; split; · next he=>
        simp_rw [ mul_left_comm (↑(p _):ℂ) _, ← Finset.mul_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sum, polar_transverse ]; simp
    simp only [ mul_zero, Finset.sum_const_zero]

structure GoodAim (m:ℕ) (F : Mob G) : Prop where
    paid : Goods 2 F
    sym (p q: SectorP m)(i j:Shaft G m): aim F p q i j= aim F q p j i
    direct (p q:SectorP m)(j:Shaft G m): stableA p (fun i=> aim F p q i j)

lemma witness (X:Pupil)(p q: SectorP m)(i j:Shaft G m): aim (enrol X G 0).symbol p q i j=∑ t:Name G,(X.density t.1:ℂ)*(Cur X t p i*Cur X t q j):= takesA X m i.2 j.2 i.1 j.1 p q

lemma GoodAim.mark (X:Pupil): GoodAim m (enrol X G 0).symbol where
    paid:=(enrol X G 0).slots
    sym p q i j:= by simp_rw [witness]; apply Finset.sum_congr rfl; intro t _; ring
    direct p q j:= by
        intro a; simp_rw [witness, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun t _=>?_;
        let f(i:L m):=Cur X t p (a,i); obtain ht: ∑ i:L m,(p i:ℂ)*f i=0:= antenna_right p X t a; let c:ℂ:=X.density t.1;
        change (∑ i:L m,(p i:ℂ)*(c*( f i* Cur X t q j)))=_; simp_rw [mul_left_comm (_:ℂ) c,← Finset.mul_sum, show ∀ i:L m,(p i:ℂ) * ( f i* Cur X t q j) = (p i:ℂ)*f i* Cur X t q j from fun i=> (mul_assoc ..).symm, ← Finset.sum_mul,ht,zero_mul,mul_zero]

include g
lemma oriented (hp:GoodAim m W) (d:ℂ)(he:Radiant K (-p) d)(i j:Shaft G m):
    slotTake K (R G).symbol W (rod i) (rod j) p q = (Coupling G*p.sq*d)*aim W p q i j := by
    let f(a:Shaft G m):= aim W p q a j; let L(a:Shaft G m):=aim (R G).symbol (-p) p a i
    have ht:= hp.direct p q j; unfold slotTake; rw [he.all]; swap; · intro a b h; rw [h]; ring
    simp only [ show ∀ i:Shaft G m, parity (rod i)=false from fun _=>rfl,cross_false,one_mul ];
    have hu(a:Shaft G m): ∑ b:Shaft G m,2*K m (rod a) (rod b) (-p)* L a*f b=(L a*f a)*d := by
        simp_rw [mul_assoc (2*K m (rod a) _ _),mul_left_comm _ (L a),← Finset.mul_sum]; rw [he.focus _ f ht.mirror]; ring
    change (∑ a:Shaft G m,∑ b:Shaft G m,2*K m (rod a) (rod b) (-p)*L a*f b)=_; simp_rw [hu,← Finset.sum_mul]; rw [show (∑ a:Shaft G m,L a*f a)= _ from PoleAction g p i f ht]; unfold f; ring
lemma branched (hp:GoodAim m W)(d e:ℂ)(h:Radiant K (-p) d)(he:Radiant K (-q) e)(i j:Shaft G m): aim (bridgeG K (R G).symbol W) p q i j=
    Coupling G*( p.sq*d+ q.sq*e)*aim W p q i j:= by
    unfold aim armI; rw [ branching (show Goods 2 (R G).symbol from (ghostR G).slots) hp.paid, oriented p q g hp d h, oriented q p g hp e he, show parity (rod i)=false from rfl,cross_false, hp.sym q p ]; change _ = _*aim W p q i j; ring

def Highβ (G:Gauge)(p:SectorP m)(s:ℝ):ℂ:= Coupling G * p.sq * evenPart p s
def Highβ' (G:Gauge)(p:SectorP m)(s:ℝ):ℂ:= Coupling G * p.sq * shining p s
omit g in
theorem highJet (G:Gauge)(p: SectorP m)(s:ℝ): HasDerivAt (Highβ G p) (Highβ' G p s) s:= (even_jet p s).const_mul _
omit g in
theorem high_gone (G:Gauge): Tendsto (Highβ G p) atBot (𝓝 0):= by unfold Highβ; simpa only [mul_zero] using (even_gone p).const_mul (Coupling G*p.sq)
omit g in
lemma high_parity (G:Gauge)(s:ℝ): Highβ G (-p) s= Highβ G p s:= by simp [Highβ,even_parity]

variable (s:ℝ)(x:I)
theorem arm_along (X:Pupil) (i j : Shaft G m): aim (absNom μ (bed (armBranch X (vertex (R G)))) s x) p q i j=
    (Highβ G p s+ Highβ G q s)*aim (enrol X G 0).symbol p q i j:= by
    rw [ before_base μ s x (firstResult ..) ]; obtain ht:= (selected_radial false (R G) (enrol X G 0) s).2
    simp only [factor,Bool.false_eq_true, ↓reduceIte, Complex.ofReal_one,one_smul] at ht; rw [ ht, branched p q g (GoodAim.mark X) _ _ (shell_act (-p) s) (shell_act (-q) s) ]; unfold Highβ; simp_rw [even_parity]; ring

lemma near_tree (F:Planted G I true)(hp:GoodAim m (absNom μ F s x))(i j:Shaft G m): aim (absPush μ (Planted.B Q (vertex (R G)) F) s x) p q i j=
   (Highβ' G p s+Highβ' G q s)* aim (absNom μ F s x) p q i j:= by
    rw [ pushedB μ s x, bulkAtom ]; have ht : pulse 4 s (cursor false).half= cleanJet G s:= (pulse_line false s 4 _).trans (congr_arg (pickLine false) ( pA G s )); rw [ ht, branched p q g hp _ _ (jet_act (-p) s) (jet_act (-q) s) ]; simp_rw [ Highβ', shine_parity ]; ring
end YM.MS.ScaleForest.Triangle
