import YM.MS.ScaleForest.Azimuth
/-!
# Removal of poles for lift proofs (also a weighted version of `Stay`)

To work at finite IR and to control the other limits when the local vertex
subtraction has a pole multiplying the *integral of a quotient*, one needs
uniform control of continuation costs in vertices. Use powers of z, then
if negative coefficients canceled, promote the INTEGRANDS (not individually
expanding at dimension 4) to full `Waves` estimates. `Iris` is the germwise
criterion on a family with many parameters besides z. Also for the
one-source series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {X Y : Curtain G I} {R T a b S : ℝ} {p : ℤ} {Z:ℂ} {n k m : ℕ}

abbrev Iris (F H:Curtain G I):= F =ᶠ[dotty] H
abbrev taper (n:ℕ)(F:Curtain G I) : Curtain G I:= fun z=> z^n • F z
def populated (F:Curtain G I) : Curtain G I:= open Classical in fun z=> if z=0 then fun s x=> ruby (fun z=>F z s x) 0 else F z
abbrev Gazed (F:Curtain G I) := ∀ s i, Live (fun z=> F z s i)
omit [TopologicalSpace I] in
theorem utaper {F G':Curtain G I}(h:Iris F G')(n:ℕ): Iris (taper n F) (taper n G'):= h.mono fun _ hi=> congr_arg _ hi
omit [TopologicalSpace I] in
theorem popTie (F:Curtain G I): Iris (populated F) F := dotty_non.mono fun _ hi=>if_neg hi
omit [TopologicalSpace I] in
theorem popOff (F:Curtain G I) (hi:Z≠0): populated F Z=F Z:= if_neg hi
omit [TopologicalSpace I] in
theorem popAt (F:Curtain G I) (p:ℝ) (i:I): populated F 0 p i=ruby (fun z=> F z p i) 0:= by unfold populated; rw [if_pos rfl]

section center
variable (hv:Waves R p Y) (he : Envelope R a b Y)
variable (hR:Enough R)(hh:∀ z∈disc R,z≠0 → taper n X z=Y z)
include hh
omit [TopologicalSpace I] in
private theorem tornX (hZ:Z∈disc R)(hi:Z≠0): populated X Z=(Z^n)⁻¹ • Y Z:= by rw [ ← hh Z hZ hi,popOff X hi]; exact (inv_smul_smul₀ (pow_ne_zero n hi) _).symm
variable (hT : 0<T)(hp : T < R)
include hT hp
omit [TopologicalSpace I] in
private theorem tornBall (u:ℝ)(i:I) (z:sphereT T): populated X z.val u i=(z.val^n)⁻¹ • Y z.val u i:= by
   obtain ht: z.val∈disc R:= Metric.closedBall_subset_ball hp (Metric.sphere_subset_closedBall z.property); have hi: ‖z.val‖=T:=by simpa only [mem_sphere,dist_zero_right] using z.property
   rw [tornX hh ht (norm_pos_iff.mp (hT.trans_le hi.ge))]; rfl
include he
omit [TopologicalSpace I] in
private theorem coneLife : sphereBudget (populated X) a b T := by
   intro J z s v; simp_rw [tornBall hh hT hp];
   let D(i:J):disc R := ⟨ (z i).val, Metric.closedBall_subset_ball hp (Metric.sphere_subset_closedBall (z i).property) ⟩;
   have hs : scaleC 0 1 (fun i=> ‖ ((z i).val^n)⁻¹‖):= by
      refine ⟨ (T^n)⁻¹,by positivity,0,fun i p he=>?_⟩; have hx: ‖(z i).val‖=T:=by simpa only [mem_sphere,dist_zero_right] using (z i).property
      dsimp only; rw [norm_inv,norm_pow,hx]; simp
   convert! fall_scale (he J D s v) hs using 1; ext; simp
omit he
include hv
private theorem coneGlobe : Sway (fun x:sphereT T×ℝ×I=> populated X x.1.val x.2.1 x.2.2) := by
   let D: sphereT T×ℝ×I→Atlas I R:= fun i=> (⟨ i.1.val,Metric.closedBall_subset_ball hp (Metric.sphere_subset_closedBall i.1.property)⟩, i.2); have ht:= repaint hv.sway D (by unfold D; fun_prop);
   have hZ (x:sphereT T): x.val≠0:= by
      have hp: ‖x.val‖=T:=by simpa only [mem_sphere,dist_zero_right] using x.property
      exact norm_pos_iff.mp (hT.trans_le hp.ge)
   simp_rw [tornBall hh hT hp]; refine Sway_smul (X:= fun x=> Y (D x).1.val x.2.1 x.2.2) (Z:=fun x:sphereT T×ℝ×I=> (x.1.val^n)⁻¹) ht ?_; exact Continuous.inv₀ (by fun_prop) (fun i=> pow_ne_zero n (hZ i.1))
omit hp hT
variable (hX : Gazed X)
include hX hR

omit hR in
private theorem coneInside (s : ℝ)(x : I) : hill (disc R) (fun z=> populated X z s x) := by
   intro m w z hz
   rcases eq_or_ne z 0 with rfl|hZ
   · obtain ht : Lift (fun z=> X z s x) (populated X 0 s x) := by rw [popAt]; exact Rub (hX s x) 0
     obtain ⟨g,V,hV,h,hU,h0⟩:=ht
     refine DifferentiableAt.congr_of_eventuallyEq (h.top m w 0 (Metric.mem_ball_self hV)) ?_; obtain ⟨U,h_U,hg⟩:= dotty_mem.mp hU; filter_upwards [Metric.ball_mem_nhds (0:ℂ) h_U] with z ht; rcases eq_or_ne z 0 with rfl|he
     · rw [h0]
     rw [popOff X he]; rw [ show g z=X z s x from hg z ht he ]
   have ht:∀ᶠ u in 𝓝 z, u∈disc R ∧ u≠0:= Eventually.and (p:=fun u=>u∈disc R) (q:=fun u=>u≠0) (Metric.isOpen_ball.mem_nhds hz) ((isOpen_ne_fun continuous_id continuous_const).mem_nhds (by exact hZ))
   refine DifferentiableAt.congr_of_eventuallyEq ( ((show DifferentiableAt ℂ (fun z : ℂ=> z^n) z by fun_prop).inv (pow_ne_zero n hZ)).mul ((hv.hol s x).top m w z hz)) (?_)
   filter_upwards [ht] with z h; rw [tornX hh h.1 h.2]; rfl
include he hp hT

theorem restoreDisk (hS:0<S)(ht:S<T) : Enough S ∧ Envelope S a b (populated X)∧ Waves S p (populated X) := by
   obtain hs := enough_le hR hS (le_trans ht.le hp.le);
   have hA(s x):= coneInside hv hh hX s x
   have hB := coneGlobe hv hh hT hp;
   obtain h:= restoreEnvelope hT hp ht hA (coneLife he hh hT hp)
   have hol (s:ℝ) (x:I) : Hol (disc S) (fun z=> populated X z s x) := by
      refine ⟨ fun c T' hx he=>?_, fun m w z hz=> hA s x m w z (Metric.ball_subset_ball (ht.trans hp).le hz)⟩
      exact pay_price (h _ (fun z : closedBall c T'=> (⟨ z.val,he z.property⟩:disc S)) (fun _=>s) (fun _=>x)) (posLevy a b s) (b:=fun _=>1) (by intro i; rw [mul_one])
   have hU (s x): Shine.Wind (fun z=> populated X z s x) dotty (populated X 0 s x):= Shine.Wind.cake (hol s x) hS
   have hσ z (hZ:z∈disc R)(hn:z≠0) (s:ℝ)(x:I) : Sturdy false (populated X z s x)∧ Goods p (populated X z s x) := by rw [tornX hh hZ hn]; exact ⟨ Sturdy_scale (hv.token _ hZ _ _) _, (good p G).smul_mem ((z^n)⁻¹) (hv.funds _ hZ _ _)⟩
   have h_e (s x): ∀ᶠ z in dotty, Sturdy false (populated X z s x) ∧ Goods p (populated X z s x):= by
     filter_upwards [dotty_bill hR.1,dotty_non] with z h hZ; exact hσ z h hZ s x
   refine ⟨ hs,h,⟨fun m w=> ?_, hol,fun z hz s x=> ?_,fun z hz s x=>?_⟩⟩
   · exact Cauchy_dual hT (T:=T) (R:=R) (by assumption) ht (F:=fun (i:Atlas I S) z=> populated X z i.2.1 i.2.2 m w) (fun i=> hA i.2.1 i.2.2 m w) ((hB m w).comp (show Continuous (fun i:Atlas I S×sphereT T=>(i.2,i.1.2)) by fun_prop)) Prod.fst continuous_fst
   · rcases eq_or_ne z 0 with rfl|hZ; exact Shine.Wind.time (hU s x) (Eventually.mono (h_e s x) (fun _ hv=> hv.1)); exact (hσ z (Metric.ball_subset_ball (le_trans ht.le (by linarith)) hz) hZ s x).1
   rcases eq_or_ne z 0 with rfl|hZ; exact Shine.Wind.peerG (hU s x) (Eventually.mono (h_e s x) (fun _ hv=> hv.2)); exact (hσ _ (Metric.ball_subset_ball (le_trans ht.le (by linarith)) hz) hZ s x).2
end center

variable (hR:Enough R)
include hR
theorem reduceLift (hv:Waves R p Y) (he:Envelope R a b Y) (ht:Iris (taper n X) Y)
    (h:Gazed X) : ∃ R, Enough R∧Waves R p (populated X)∧Envelope R a b (populated X) := by
   obtain ⟨S,hS,hs⟩:= dotty_mem.mp ht; let Q:=min R S; have hQ:= lt_min hR.1 hS; let M:= enough_le hR hQ (min_le_left ..); obtain ⟨he', hu,hW⟩:= restoreDisk (hv.shrink (min_le_left R S)) (he.shrink (min_le_left ..)) M
      (fun z (hz:z∈disc Q)=> hs z (Metric.ball_subset_ball (min_le_right ..) hz)) (half_pos hQ) (half_lt_self hQ) h (half_pos (half_pos hQ)) (half_lt_self (half_pos hQ)); exact ⟨ _,he', hW,hu ⟩
end YM.MS.ScaleForest
