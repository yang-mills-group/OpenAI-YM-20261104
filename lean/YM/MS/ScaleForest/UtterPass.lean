import YM.MS.ScaleForest.UtterBase
/-!
# Add the two scale-order classes in the push of the tree of the ghost example

Actually evaluating the **quotient outside the local ghost pole tensor**.
Produce its two-survivor tensor kernel at rank two. Include both X and Y
lines to the local V and know the exact momentum of the external A-slots
(also intentionally probe nonzero net momentum because these are marked).
This works on the contracted `bubble` example (ranks in
the complete all-orders calculation can be different). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I:Type} (X Y:Pupil) (x:E4) (p q:QP) (i j:Shaft G 0)(s:ℝ)

lemma truthHue (z:Ω G) (w:QP) : salute₂ X Y z.1 z.2 x w s= Highβ G (m:=0) w s * salute' X Y z.1 z.2 x w s:= mul_comm ..

abbrev shiftedX (G:Gauge)(s:ℝ) (p q:QP): ℂ:= Highβ G (m:=0) p s+ Highβ G (m:=0) q s
-- `proofWalk` includes placements on both marks.

abbrev try_x (z:Ω G):= Highβ G (m:=0) p s * dotV X Y x z s + (2:ℂ)⁻¹ * dotM X Y x z s
-- integrand relation
theorem x_ready (z:Ω G) :
    let f:= Christ X Y x p q s (shiftedX G s) (fun _ _=>1) z
    Integrable f planeF∧(∫ w,f w∂planeF)=try_x X Y x p s z:= by
    intro f
    let k:= (2:ℂ)⁻¹; let F(w:QP):= salute' X Y z.1 z.2 x w s; let H(w:QP):= salute₂ X Y z.1 z.2 x w s; let c:=Highβ G (m:=0) p s
    have h(w:QP): f w=c*F w+H w:= by unfold f Christ H shiftedX F c; rw [truthHue X Y x s]; ring
    rw [funext h]; obtain hx:= (sunSupported X Y z.1 z.2 x s).const_mul c; obtain ht:= moonSupported X Y z.1 z.2 x s; refine ⟨ hx.add ht,?_⟩; rw [integral_add hx ht,integral_const_mul]; change _ =c*(∫ w,F w∂planeF)+(2:ℂ)⁻¹*( 2*∫ w,H w∂planeF ); ring

theorem y_ready (z:Ω G) :
    let f:= Christ X Y x p q s (fun _ _=>1) (shiftedX G s) z
    Integrable f planeF∧(∫ w,f w∂planeF)=try_x X Y x q s z:= by
    intro f; obtain ht:= x_ready X Y x q p s z; have he : f= Christ X Y x q p s (shiftedX G s) (fun _ _=>1) z:=by funext w; simp [f,shiftedX,Christ, high_parity (m:=0)]
    rw [he]; exact ht

abbrev proofWalk (p:QP)(q:QP)(z:Ω G):= shiftedX G s p q * sunV X Y x z s + moonV X Y x z s


variable [TopologicalSpace I] [FirstCountableTopology I] {A:I→QP} (y:I) (μ:ℝ)
   (hp: Theater.out x=A y)
variable (h:AdmittedGap A)(g:G.Simple)
include hp g
local notation "d"=> cursor false

lemma near_sum :
  let V:= vertex (ghostR G);
  aim (absPush μ (nearX X Y A V) s y) p q i j+aim (absPush μ (nearY X Y A V) s y) p q i j =
     stained X Y x p q i j fun z=> shiftedX G s p q* dotV X Y x z s+dotM X Y x z s := by
    intro V; let Xp:Planted G I false:=bed (originPin X G); let Wp:Planted G I false:= bed (armBranch X V); let Yp:Planted G I false:= bed (originPin Y G); let Up:Planted G I false:= bed (armBranch Y V)
    change aim (absPush μ (Planted.P d A Wp Yp) s y) p q i j+aim (absPush μ (Planted.P d A Xp Up) s y) p q i j=_
    have hX(W:Pupil): Portrait W (absNom μ (bed (originPin W G)) s y) (fun _ _=> 1):= by rw [pinnedAtom]; exact Por_base ..
    rw [ pushedP μ s y d (show Wp.Stand from trivial) (show Yp.Stand from trivial), pushedP μ s y d (show Xp.Stand from trivial) (show Up.Stand from trivial),prim_0 G s,← hp ];
    rw [expense_cross x p q s μ (Planted.observing μ s y Wp trivial).1 (Planted.observing μ s y Yp trivial).1 (Por_left s X y μ g) (hX Y) i j (T:=fun p _=>try_x X Y x p s) ?_, expense_cross x p q s μ (Planted.observing μ s y Xp trivial).1 (Planted.observing μ s y Up trivial).1 (hX X) (Por_left s Y y μ g) i j (T:=fun _ q=>try_x X Y x q s) ?_ ]; -- rw hX defeq
    · unfold tincture stained; rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun z _=> by unfold try_x shiftedX tinct; ring)
    all_goals first| exact fun p q z=> x_ready X Y x p q s z | exact fun p q z=> y_ready X Y x p q s z

include h

-- state as explicit sum over species slots; easier solve too.
theorem rankTwo :
    let V:= vertex (ghostR G); aim (absNom μ (nearX X Y A V) s y) p q i j +aim (absNom μ (nearY X Y A V) s y) p q i j +aim (absNom μ (nearB X Y A V) s y) p q i j =
       stained X Y x p q i j (proofWalk X Y x s p q) := by
    let V:= vertex (ghostR G); dsimp only
    let P:= nearX X Y A V; let S:= nearY X Y A V; let T:= nearB X Y A V; have H:=hiredWalk X Y A V h
    let aimF (U: Mob G): ℂ:= aim U p q i j
    let F(W:Planted G I true)(s:ℝ):= aimF (absNom μ W s y); let J(t:ℝ):= F P t+F S t+ F T t
    let f(t:ℝ):= stained X Y x p q i j fun z=> Highβ' G (m:=0) p t*sunV X Y x z t+ Highβ' G (m:=0) q t *sunV X Y x z t+shiftedX G t p q*dotV X Y x z t+dotM X Y x z t
    have he (t:ℝ) : HasDerivAt J (f t) t:= by
       have h_F(W:Planted G I true)(h:W∈ streets X Y A V) : HasDerivAt (F W) (aimF (absPush μ W t y)) t:= Speed μ t y _ (H W h)
       convert! ((h_F P (by simp [P,streets])|>.add (h_F S (by simp [S,streets]))).add (h_F T (by simp [T,streets]))) using 1
       unfold T S P aimF nearB; rw [ near_sum X Y x p q i j t y μ hp g, near_tree p q g t y (μ:=μ) _ (mid_right X Y x t y μ hp h G) i j, mid_progress X Y x p q i j t y μ hp h ]; unfold f stained; simp only [ Finset.mul_sum, ← Finset.sum_add_distrib ]; exact Finset.sum_congr rfl fun i _=>by ring
    let W(s':ℝ):= stained X Y x p q i j (proofWalk X Y x s' p q)
    have hx(t:ℝ): HasDerivAt W (f t) t:= by
       let D(z:Ω G)(t:ℝ):= Highβ' G (m:=0) p t*sunV X Y x z t+ Highβ' G (m:=0) q t *sunV X Y x z t+shiftedX G t p q*dotV X Y x z t+dotM X Y x z t
       apply stain_side X Y x p q i j t (V:=fun z t=> proofWalk X Y x t p q z) (F:=D); intro z
       convert! ((((highJet (m:=0) G p t).add (highJet (m:=0) G q t)).mul (sunSpeed X Y z.1 z.2 x t)).add (moonSpeed X Y z.1 z.2 x t)) using 1; unfold D shiftedX dotM sunV dotV; dsimp only [Pi.add_apply]; ring
    have Hx(z:Ω G): Tendsto (fun s:ℝ=> proofWalk X Y x s p q z) atBot (𝓝 0):= by
       unfold proofWalk shiftedX; simpa only [zero_mul,mul_zero,add_zero] using ((((high_gone (m:=0) p G).add (high_gone (m:=0) q G)).mul (sunStart X Y z.1 z.2 x ( point_gap x y hp h))).add (moonStart X Y z.1 z.2 x (point_gap x y hp h)))
    have ht(W:Planted G I true): Tendsto (F W) atBot (𝓝 0):= StartZero μ y _
    apply congr_fun (ode_solver he hx ?_ ?_) s; simpa only [add_zero] using ((ht P).add (ht S)).add (ht T); exact fade_stain X Y x p q i j _ Hx
end YM.MS.ScaleForest.Triangle
