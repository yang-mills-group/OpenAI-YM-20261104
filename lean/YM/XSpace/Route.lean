import YM.XSpace.Abridged
import YM.XSpace.ReflectionCov

/-!
# Tangent-chart setup for cubic gauge motion

We **do not condition the Wilson start** on a harmonic cut; transport stays at the
trivial saddle with inversion built in. Use rank on directed link and vertex quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Function Lattice Next.Rank.Normal Module
open scoped BigOperators Topology
variable {G : Gauge} {R : Period} (T : R.Tree)
abbrev Carrier (G : Gauge) := T.Field G × (T.Nonroot → G.Color)
abbrev Knobs (G : Gauge) := T.Key G ⊕ ((_ : T.Nonroot) × G.ColorIndex)

def rise : (T.Nonroot → G.Color) →ₗ[ℝ] (R.Vertex → G.Color) where
  toFun p x:= if h:x≠T.root then p ⟨x,h⟩ else 0
  map_add' p q:=funext fun x=>by by_cases h:x=T.root <;> simp [h]
  map_smul' p q:=funext fun x=>by by_cases h:x=T.root <;> simp [h]
@[simp] lemma rise_at (p:T.Nonroot→ G.Color) (x:T.Nonroot): rise T p x=p x:=by simp [rise,x.property]
@[simp] lemma rise_root (p:T.Nonroot→ G.Color): rise T p T.root=0:=by simp [rise]

def born : Carrier T G→ₗ[ℝ] (R.Sites→ G.Color):= LinearMap.pi fun x => (LinearMap.proj (R.vertex x) ∘ₗ rise T) ∘ₗ LinearMap.snd ℝ _ _
def route : Carrier T G→ₗ[ℝ] LogLinks (Per R.side) G:= T.covering.comp (LinearMap.fst ℝ _ _)+grad.comp (born T)
lemma born_at (x:Carrier T G) (v:R.Sites) : born T x v= rise T x.2 (R.vertex v):=rfl
lemma routes (x:Carrier T G):route T x= T.covering x.1+grad (born T x):=rfl
lemma from_hor (x:T.Field G): route T (x,0) = T.covering x:=by rw [routes,show born T (x,0)=0 from funext fun i=> by rw [born_at,map_zero]; rfl,map_zero,add_zero]

-- compare the Hessian convention
lemma grad_eq_deriv (P : Period) : grad (G:=G) (R:=Per P.side)=P.derivative:= LinearMap.ext fun _=>rfl

lemma route_curl (x:Carrier T G): R.curl (route T x)=R.curl (T.covering x.1):= by rw [routes,map_add,grad_eq_deriv R, R.curl_derivative,add_zero]
lemma curl_is (R:Period) (u:R.Bonds→G.Color) (p:Face (Per R.side)): linearFace p u=R.curl u p:= angular ..
lemma route_face (x:Carrier T G) (p : Face (Per R.side)): linearFace p (route T x)=T.linearCurl x.1 p:=by rw [curl_is R,route_curl]; rfl

def Legit (R:Period) (A : R.Bonds→G.Color): Prop:= R.mirrorLink A=A
lemma legit_reflect {x:R.Bonds→G.Color} (h: Legit R x) (i:R.Bonds): x (R.reflect i)= -x i:=by rw [← neg_inj]; rw [← R.mirror_apply,h,neg_neg]
lemma legit_route (x:Carrier T G): Legit R (route T x):=by
  unfold Legit; rw [routes,map_add,T.mirrors,grad_eq_deriv R]; congr 1; exact R.mirror_derivative (rise T x.2)
lemma legit_complete (x:R.Bonds→G.Color) (h:Legit R x): ∃ y:Carrier T G, route T y=x:=by
  obtain ⟨u,hu⟩:= T.complete _ h; set y:= x-T.covering u
  have hh : Legit R y:=by unfold Legit y; rw [map_sub,h,T.mirrors]
  obtain ⟨v,hv⟩:= R.exact_of_odd y (legit_reflect hh) (by unfold y; rw [map_sub,hu,sub_self])
  let z:= (u,fun i:T.Nonroot=> v i.val-v T.root)
  have hp a : rise T z.2 a=v a-v T.root:=by by_cases h:a=T.root; simp [h]; exact rise_at T z.2 ⟨a,h⟩
  refine ⟨z, Eq.trans (routes T z) ?_⟩; rw [show grad (born T z)=y from ?_]; swap
  · funext i; rw [hv,grad_at,R.derivative_at,born_at,born_at,hp,hp,comp_apply,comp_apply]; abel
  change T.covering u+(x-T.covering u)=_; abel
lemma preserve_zero (x : Carrier T G) (h: route T x=0):x=0:=by
  have h1:x.1=0:= T.no_modes x.1 (by rw [← route_curl,h,map_zero]); apply Prod.ext h1
  have he:= routes T x; rw [h1,map_zero,zero_add,h] at he
  have hp (e:R.Link): rise T x.2 (R.dst e)=rise T x.2 (R.src e):= sub_eq_zero.mp (show grad (born T x) e.val=0 from congr_fun he.symm e.val)
  have ht (n:ℕ): ∀ y,T.rank y=n→ rise T x.2 y=0:= by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hN; by_cases H:y=T.root; rw [H,rise_root]
      specialize hp (T.edge y H); rcases T.joins y H with ⟨a,b⟩|⟨a,b⟩ <;> rw [a,b] at hp
      · exact hp.symm.trans (ih _ (hN ▸ T.closer y H) _ rfl)
      exact hp.trans (ih _ (hN ▸ T.closer y H) _ rfl)
  exact funext fun i: T.Nonroot=>Eq.trans (rise_at _ _ _).symm (ht (T.rank i) i rfl)
lemma inject_route : Injective (route T (G:=G)):= fun i j h=> sub_eq_zero.mp (preserve_zero T _ (by rw [map_sub,h,sub_self]))

-- left inverse with exact choice on anti-invariant complement
def polarized (R:Period) : Module.End ℝ (R.Bonds→G.Color):=(1/2:ℝ) • (LinearMap.id+R.mirrorLink)
lemma legit_polar (A:R.Bonds→G.Color): Legit R (polarized R A):=by unfold Legit polarized; simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.id_coe, id_eq]; rw [map_smul, map_add,R.mirror_link_twice,add_comm]
lemma polar_keeps (A:R.Bonds→G.Color) (h:Legit R A): polarized R A=A:=by unfold polarized; simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.id_coe,id_eq]; rw [h]; module

def park : (R.Bonds→ G.Color) →ₗ[ℝ] Carrier T G :=
  (LinearMap.exists_leftInverse_of_injective (route T) (LinearMap.ker_eq_bot_of_injective (inject_route T))).choose.comp (polarized R)
lemma park_undo (x:Carrier T G): park T (route T x) = x := by unfold park; rw [LinearMap.comp_apply, polar_keeps _ (legit_route T x)]; exact DFunLike.congr_fun (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot_of_injective (inject_route (G:=G) T))).choose_spec _
lemma undo_park (x:R.Bonds→G.Color):route T (park T x)=polarized R x:=by
  obtain ⟨u,hu⟩:= legit_complete T _ (legit_polar x)
  have h : park T x= park T (route T u) := by rw [hu]; unfold park; rw [LinearMap.comp_apply,LinearMap.comp_apply,polar_keeps _ (legit_polar x)]
  rw [h,park_undo,hu]

def nobasis (G : Gauge):= Pi.basis (fun _ : T.Nonroot => (basisC G).toBasis)
abbrev axisB (G : Gauge): Basis (Knobs T G) ℝ (Carrier T G):= (T.basis G).prod (nobasis T G)
lemma axisB_hor (i:T.Key G): axisB T G (.inl i)=(T.basis G i,0):=by rw [axisB,Basis.prod_apply]; rfl
lemma axisB_vert (i): axisB T G (.inr i)=(0, nobasis T G i):=by rw [axisB,Basis.prod_apply]; rfl
end YM.XSpace.Chart2
