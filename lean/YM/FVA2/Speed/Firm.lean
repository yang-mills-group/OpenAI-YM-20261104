import YM.FVA2.Speed.Fast
import YM.XSpace.Carpet
/-!
# Uniform position/test estimates in the Mesh convention

Each such fixed K. `Strength` for the points already in `welcome`
on all `Front`, and `Labor` including the `TestBudget`. See `way`
about proving the second one uniformly even *across* the points used
in smearing; uses the key smoothness estimate on `Damp` (supplied in
`ahead`, not assuming any position smoothness of a discrete lattice
observable).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed
open XSpace XSpace.Expense XSpace.Cirrus XSpace.TestBudget MS MS.Tide Lattice
open Asymptotics Set Function Metric Filter MeasureTheory Real
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}{K:Set (Points n)}{I E:Type*}[NormedAddCommGroup E]
local notation "ɛ"=> MS.Tide.mildG
/-- Fits uses center (`welcome`) not lattice profile condition beyond `Front`.
 Index set does not encode mesh-size-dependent choices for K.
-/
def Pose (K:Set (Points n)) : Filter (XSpace.Cirrus.Sample n):= comap grab Front ⊓ 𝓟 {i|welcome i ∧ familiar i∈K}
local notation "Z"=> Sample n
local notation "κ"=> Pose K
lemma Motion {A:Sample n→Prop}: (∀ᶠ i in κ,A i) ↔ (∀ᶠ m in Front,∀ i:Sample n,grab i=m→welcome i→familiar i∈K→ A i):= by unfold Pose; rw [ eventually_inf_principal,eventually_comap ]; simp only [Set.mem_setOf_eq,and_imp]
lemma Each (K:Set (Points n)): ∀ᶠ i in Pose K,welcome i ∧ familiar i∈K:= Motion.mpr ( Eventually.of_forall (fun _ _i _h y u=> ⟨y,u⟩ ) )
lemma grows (K:Set (Points n)): Tendsto grab (Pose K) Front:= tendsto_iff_comap.mpr inf_le_left
lemma travels (K:Set (Points n)) : Stretched (Pose K) grab:= frontier.wider ( grows K )
-- eventual-powers in recommended q units
section point
variable {f:Sample n→E}{Y:Points n→E}
abbrev Contacts (K:Set (Points n))(f: Sample n→ E) (Y:Points n→E):= Fast (Pose K) grab f (Y ∘ familiar)
def Strength (K:Set (Points n))(f:Sample n→ E)(Y:Points n→E): Prop:=
    ∃ C:ℝ, 0<C ∧ ∀ᶠ m in Front, ∀ i:Sample n,
      grab i=m → welcome i → familiar i ∈ K → ‖f i-Y (familiar i)‖≤ C*chip i.F
lemma cartel : Strength K f Y↔ Contacts K f Y:= by
    constructor; · rintro ⟨C,hC,h⟩; exact Fast.put C ( Motion.mpr h )
    intro h; obtain ⟨C,hC,h⟩:= Fast.bounds ( l:=Pose K ) h; exact ⟨ C,hC, Motion.mp h ⟩
lemma essence (V:Set (Points n))(p:Points n→E)(K:Set (Points n))(h:IsCompact K)(hk: K⊆ V)(hc:ContinuousOn p V): Expense.Cap (Pose K) (p ∘ familiar):= ( Sharp.of_bounds K h (( Each K ).mono fun _ hi=> hi.2) ( hc.mono hk ) ( Fast.refl _ grab _ ) ).quote
end point
section test
variable {Y:Points n→ℂ}{f:Sample n→ℂ}(h:Strength K f Y)(hK:IsCompact K)(hk:K⊆conf n)(hC:∀ v∈conf n,ContDiffAt ℝ ∞ Y v)
def Labor (K:Set (Points n))(x:Mesh→Test n→ℂ)(y:Test n→ℂ):Prop:=
    ∃ C:ℝ, 0<C ∧ ∀ᶠ m in Front, ∀ t:Test n, tsupport t⊆K →
      ∀ b:ℝ, TestBudget.Bound t b → ‖x m t-y t‖≤ b*C*chip m
-- local m comparison by C1 global on conf.Y
include hC
local notation "Ω"=> Points n
set_option maxHeartbeats 600000 in
lemma way (p:XSpace.Mesh) (V:Set (Points n))(C r:ℝ)(hp:p.spacing≤1)(hu:p.Fits (closedBall (0:Points n) (r+4*n))) (k:p.spacing≤ chip p)(t:Test n)(ht: tsupport t⊆V)(hr:∀ x∈V, ‖x‖≤r)(A:Centered f)(s: Four ℝ)(hs:s∈p.Box)(hc:0≤C){M b:ℝ}(hM:0≤M)(hb:TestBudget.Bound t b)
 (h0 : ∀ x : p.Tuple (n:=n), p.rel (p.back x) s∈V→ ‖f ⟨p,p.back x,s⟩- Y ( p.rel (p.back x) s )‖≤ C*chip p)
 (hm : ∀ x y:Points n, ‖Damp t Y x -Damp t Y y‖ ≤ b*M*dist x y):
 ‖XSpace.Cirrus.paths p t f s-t.applyTo Y‖≤ b*((C+(4*n:ℝ)*M)*volume.real (closedBall (0:Points n) (r+4*n)))*chip p:= by
  set W:=closedBall (0:Points n) (r+4*n)
  let q:=Damp t Y; let R:=p.levels s ( board p t f s ); let P := b*(C+(4*n:ℝ)*M)*chip p
  have hb' : 0≤b:=bound_nonneg t hb; have hP: 0≤P:=by unfold P; have hc':0< chip p:= Speed.f_pos id p; positivity
  have hZ (x : Points n) (h : x∉ V) : t x=0:= image_eq_zero_of_notMem_tsupport (fun hi=>h (ht hi))
  have hbq (x : Points n) (h : x∉ V): q x=0:=mul_eq_zero_of_left (hZ x h) _
  have hut (z): z∈W ↔ ‖z‖≤r+4*n:=by rw [mem_closedBall,dist_zero_right]
  have he (z) : ‖R z-q z‖ ≤ P ∧ (z∉ W→ R z-q z=0) := by
    by_cases h:∃ x:p.Tuple (n:=n),z∈p.cell s (p.back x)
    · obtain ⟨x,hx⟩:=h; let a:=p.rel (p.back x) s; have he := p.upper_corner s hx; have hh: dist a z≤ (4*n:ℝ)*chip p:=he.trans ( mul_le_mul_of_nonneg_left k (by positivity) )
      let B:ℂ:=f ⟨ p,p.back x,s⟩; have hg : R z=t a*B:= Eq.trans (p.stair_at s z hx) (congr_arg (t a*·) (A p (p.back x) s).symm)
      have h0 : ‖R z-q a‖ ≤ b*C*chip p:= by
        rw [hg,show q a=t a*Y a from rfl, ← mul_sub,norm_mul]; by_cases h:a∈V
        · rw [mul_assoc b]; exact mul_le_mul (hb a).1 (h0 x h) (norm_nonneg _) hb'
        rw [hZ a h,norm_zero,zero_mul]; have hz : 0<chip p:= Speed.f_pos id p; positivity
      constructor
      · calc
          _ ≤ ‖R z-q a‖ + ‖q a-q z‖ := by rw [← sub_add_sub_cancel (R z) (q a) (q z)]; exact norm_add_le ..
          _ ≤ b*C*chip p + b*M*((4*n:ℝ)*chip p):= by exact add_le_add h0 ((hm a z).trans (mul_le_mul_of_nonneg_left hh (by positivity)))
          _ = P:= by unfold P; ring
      intro hu'; rw [hg,hZ a (fun h=> hu' ((hut z).2 (Mesh.norm_near hp (hr a h) (le_trans (le_of_eq (dist_comm ..)) he)))),zero_mul,hbq z (fun h=> hu' ((hut z).2 ((hr z h).trans (by simp)))), sub_self]
    rw [hbq z (fun H => h (p.gained s hp hs hu z (hr z H))),show R z=0 from p.stair_off s z (fun x hx=> h ⟨x,hx⟩)]; simp [hP]
  change ‖(∫ z,R z)-(∫ z,q z)‖≤_
  rw [← integral_sub (p.integrable_stair ..) (TestBudget.integral_pays t Y hC),← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=W) (fun z=> (he z).2)]; exact (norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..|>.measure_lt_top) (fun x _=> (he x).1)).trans_eq (by unfold P W; ring)
include h hK hk
lemma ahead (A:Centered f): Labor K (fun p t=> Deposit p f t) (fun t=> t.applyTo Y):= by
    obtain ⟨C,hC0,H⟩:=h; obtain ⟨r,hr⟩:= ( hK.image continuous_norm ).bddAbove; obtain ⟨M,hM,h⟩:= TestBudget.global hK hk Y hC; let W:= closedBall (0:Points n) (r+4*n); let a:= volume.real W; let D:= ( C+(4*n:ℝ)*M )*a; have hd:0≤D:=by unfold D a; positivity
    refine ⟨D+1,by positivity,?_⟩; filter_upwards [H,Mesh.fits_compact frontier W (isCompact_closedBall ..),frontier.smaller] with p hp ht h' f' hf b hb; refine homeward_price p f' f _ _ (fun c hc=>?_); have hK0:p.spacing≤ chip p:= by have hs:= Real.rpow_le_rpow_of_exponent_ge ( actual id p ) h' ( show ɛ≤1 from by unfold mildG High.eps_gain; norm_num); rw [Real.rpow_one] at hs; exact hs
    exact ( way hC p K C r h' ht hK0 f' hf (fun x hx=> hr (Set.mem_image_of_mem _ hx)) A c hc hC0.le hM hb (fun v hx=> hp ⟨p,p.back v,c⟩ rfl hc hx) (h f' hf b hb) ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show D≤D+1 from by simp) (bound_nonneg f' hb)) ( Speed.f_pos id p |>.le )) -- hC reused
omit h hK hk hC
variable {x:Mesh→Test n→ℂ}{y:Test n→ℂ}
lemma Labor.single (H:Labor K x y)(f:Test n)(hv:tsupport f⊆K): Fast Front id (fun i=>x i f) (fun _=>y f):= by
 obtain ⟨C,hC,H⟩:= H; obtain ⟨b,hb,h⟩:= TestBudget.bound_fin f; exact Fast.put (b*C) (H.mono (fun i hi=> hi f hv b h))
end test
end YM.FVA2.Speed
