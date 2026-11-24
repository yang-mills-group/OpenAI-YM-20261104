import YM.XSpace.Compat.Ride
import YM.XSpace.Tide

/-! # Bounded remote test charges and their potential Taylor limits -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Tide
open YM.XSpace.Compat.KP
open Function Filter Set Trace Scale Lattice Sail Litter Further.FreeCovariance.KP Maxwell Free Analysis
open scoped Topology BigOperators ContDiff
variable {k:ℕ} {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}

def Wave (k:ℕ)(v:Line G)(f:Radio G.Color): Prop:=∀ j, Beam (2+k) (Scale.twig j (bake v)) (f j)
def unroll (x:UnitIndex G)(j:Axis) (u:E4):G.Color:=if j=x.1.2 then Green u • Chart2.basisC G x.2 else 0
lemma emitted (x:UnitIndex G): Wave 0 (needle x) (unroll x):=by
  intro j; unfold unroll; rw [baked]; by_cases he : j=x.1.2
  · let f:= (ContinuousLinearMap.id ℝ ℝ).smulRight (Chart2.basisC G x.2); simp only [if_pos he]; rw [show Scale.twig j (Trace.φ x) = Trace.sweep (-x.1.1) (f ∘ cover) from funext fun i=> by rw [fit_value,φ,if_pos he.symm]; change cover (i-x.1.1) • Chart2.basisC G x.2= cover (-x.1.1+i) • Chart2.basisC G x.2; rw [sub_eq_neg_add]]; exact (greenBeam.map f).moved _
  simp only [if_neg he]; rw [show Scale.twig j (φ x)=0 from funext fun i=>by rw [fit_value,φ]; exact if_neg (Ne.symm he)]; exact Beam.zero
lemma riff_wave (L:Line G) (i:Axis){f:Radio G.Color}(X:Wave k L f): Wave (k+1) (riff i L) (fun j=> -grad i (f j)):=by
  intro j; simp only [riff,LinearMap.sub_apply,LinearMap.id_coe,id_eq,map_sub,slid_bake,twig_zone]; let p:= Scale.twig j (bake L)
  change Beam _ (Trace.sweep _ p - p) _; rw [show Trace.sweep (-step i) p-p=(-1:ℝ) • (Trace.sweep (-step i) (Δf i p)) from ?_,← Nat.add_assoc]; simpa only [neg_one_smul] using ((((X j).step_forth i).moved (-step i)).smul (-1))
  rw [neg_one_smul]; funext l; change p (-step i+l)-p l=-(p (-step i+l+step i)-p (-step i+l)); rw [neg_sub,show (-step i:Cover)+l+step i=l by abel]
lemma walkable (x:UnitIndex G)(l:List Axis):∃ f,Wave l.length (gate l (needle x)) f:=by induction l with
  | nil=> exact ⟨_,emitted x⟩
  | cons i l ih=> obtain ⟨f,hf⟩:=ih; exact ⟨_,riff_wave _ i hf⟩
theorem announcement (v:Line G)(h:v∈cane k G): ∃ f, Wave k v f:=by
  induction h using Submodule.span_induction with
  | mem v h=> obtain ⟨⟨x,t⟩,rfl⟩:= h; simpa only [Rudder.worth,List.length_ofFn] using walkable x (List.ofFn t)
  | zero => exact ⟨0,fun j=> by rw [map_zero,map_zero]; exact Beam.zero⟩
  | add _ _ _ _ ih ih' => obtain ⟨p,H⟩:=ih; obtain ⟨q,K⟩:=ih'; exact ⟨p+q,fun j=>by rw [map_add,map_add]; exact (H j).add (K j)⟩
  | smul a x _ ih=> obtain ⟨p,H⟩:=ih; exact ⟨a • p,fun j=> by rw [map_smul,map_smul]; exact (H j).smul a⟩
def advertise (k:ℕ)(v:Line G)(h:v∈cane k G): Radio G.Color:= (announcement v h).choose
lemma advertised (k:ℕ)(v:Line G)(h:v∈cane k G): Wave k v (advertise k v h):=(announcement v h).choose_spec

variable {p:Line G}{X:Radio G.Color} (H:Wave k p X) {ι:Type} {L:Filter ι}{x y z:ι→Cover}{u:E4}{a:ι→ℝ}
def visit (x:E4)(p:Radio F):Radio F:= fun i y=> p i (x+y)
include H
lemma visits (l:List Axis) (j:Axis)(v:E4)(hu:u+v≠0): ride l (visit u X j) v=ride l (X j) (u+v):=by
  have hx:= (H j).value _ hu; have ht: ContDiffAt ℝ ∞ (visit u X j) v:= hx.comp v (contDiffAt_const.add contDiffAt_id)
  rw [reports l ht,reports l hx]; unfold visit; rw [iteratedFDeriv_comp_add_left]
-- use at ambient coordinates n. displacement between remote line and desired mark (measured-from-line)
def coil (k:ℕ)(p:Line G)(a:ℝ)(x:Cover):Contact G:= a⁻¹^(1+k) • zone x (bake p)
lemma coiled (l:List Axis)(x y:Cover)(j:Axis)(c:ℝ): crack l (Scale.twig j (coil k p c x)) y=c⁻¹^(1+k) • crack l (Scale.twig j (bake p)) (x+y):=by unfold coil; rw [map_smul,← peaked,map_smul,Pi.smul_apply,peaked,twig_zone,peak_move]
lemma ranges (v:E4)(hp:∀ᶠ i in L,0<a i)(h:Tendsto a L (𝓝 0))(hx:Tendsto (fun i=> a i • rcast (x i)) L (𝓝 u))(hy:Tendsto (fun i=> a i • rcast (y i)) L (𝓝 v))(hu:u+v≠0)(l:List Axis)(j:Axis):
  Tendsto (fun i=> (a i)⁻¹^(1+l.length) • crack l (Scale.twig j (coil k p (a i) (x i))) (y i)) L (𝓝 (ride l (visit u X j) v)):=by
  simp_rw [coiled H,smul_smul, ← pow_add (a _ )⁻¹]; rw [visits H l _ _ hu,show 1+l.length+(1+k)=2+k+l.length by omega]; apply (H j).beams hp h (x:=fun i=> x i+y i) _ hu; simp_rw [Cross.rcast_add,smul_add]; exact hx.add hy
lemma tunes (hu:u≠0): Tuned (visit u X):= fun j=> ( (H j).value (u+0) (by simpa using hu)).comp _ (contDiffAt_const.add contDiffAt_id)
lemma enter (hp:∀ᶠ i in L,0<a i)(h:Tendsto a L (𝓝 0))(hx:Tendsto (fun i=>a i • rcast (x i)) L (𝓝 u))(hu:u≠0): AtRoots L a (fun i=> coil k p (a i) (x i)) (visit u X):= by intro l j; refine ranges H (y:=fun i=>(0:Cover)) 0 hp h hx ?_ (by simpa) l j; simpa using h.smul_const (rcast (0:Cover))
-- owe amount uniformly. clearance in physical scaled max-coordinates.
omit H in
def Clear (b:ℝ)(r:ℕ)(a:ℝ)(x:Cover): Prop := ∀ y:Cover,reach y≤r→ b ≤ a*reach (x+y)
lemma funds (b:ℝ)(hb:0<b) (l:List Axis)(j:Axis): ∃ C:ℝ,0≤C∧∀ (r:ℕ)(a:ℝ)(x:Cover),0<a→ Clear b r a x→∀ y:Cover, reach y≤r→ ‖crack l (Scale.twig j (coil k p a x)) y‖ ≤ C*a^(1+l.length):=by
  obtain ⟨C,hC,Hc⟩:= (H j).glows l; set n:= 2+k+l.length; refine ⟨C*b⁻¹^n,by positivity, fun r a x ha he y hy=>?_⟩; rw [coiled H,norm_smul,Real.norm_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left (Hc _) (by positivity : 0 ≤ a⁻¹^(1+k)))
  have hp:(1+(reach (x+y):ℝ))⁻¹ ≤ b⁻¹*a:=by specialize he y hy; set i:=reach (x+y); rw [inv_le_iff_one_le_mul₀ (by positivity)]; field_simp; linarith
  change _ ≤ _; calc
    _ ≤ a⁻¹^(1+k)*(C*(b⁻¹*a)^n):=by unfold carry; change _* (C*_ ^n) ≤ _; gcongr
    _ = _:= by rw [mul_pow,show a^n=a^(1+k)*a^(1+l.length) from by rw [← pow_add]; congr 1; omega,inv_pow]; field_simp
-- mark K condition via Stops -> finite-source support
lemma hires {r:ι→ℕ}(Xr:Tendsto r L atTop)(hp:∀ᶠ i in L,0<a i)(h:Tendsto a L (𝓝 0))(hk:Stops p)(hx:∃ b:ℝ,0<b∧∀ᶠ i in L,Clear b (r i) (a i) (x i)): Studio L a r (fun i=>coil k p (a i) (x i)):=by
  obtain ⟨b,hb,hx⟩:=hx; refine ⟨Xr,?_,?_⟩
  · intro e; let n:= p.support.sup (fun e=> reach e.1.1)
    refine eventually_all.mpr (fun j:G.ColorIndex=> ?_) |>.mono (fun i (hi:∀ j:G.ColorIndex,press (coil k p (a i) (x i)) e j=(0:G.Color) j)=> PiLp.ext hi)
    have hn : Tendsto (fun i=> a i*(n:ℝ)) L (𝓝 0):=by simpa using h.mul_const (n:ℝ)
    filter_upwards [hp,hx,hn.eventually (gt_mem_nhds hb), Xr.eventually_ge_atTop (reach e.1)] with i hi he ht hh
    specialize he _ hh; unfold coil; rw [map_smul,pressed,reverts p hk,Pi.smul_apply, zone_ap]; let q:UnitIndex G:=((x i+e.1,e.2),j); have hw: q ∉ p.support:=by
      intro H; have hh: reach (x i+e.1) ≤ n:= Finset.le_sup (f:=fun e:UnitIndex G=> reach e.1.1) H; exact ht.not_ge (he.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hh : (reach (x i+e.1):ℝ)≤ n) hi.le)) -- fix comm
    change _* ram q (deposit p)= 0; rw [ticket, Finsupp.notMem_support_iff.mp hw,mul_zero]
  intro n; let Q:=Axis × (Fin n→Axis); choose C hc Hc using fun q:Q=> funds H b hb (List.ofFn q.2) q.1; refine ⟨∑ i,C i,Finset.sum_nonneg fun i _=> hc i,?_⟩
  filter_upwards [hp,hx] with i hi hh y hy l hl j; subst n
  have he:= Hc (j,l.get) (r i) (a i) (x i) hi hh y hy; rw [show List.ofFn l.get=l from List.ofFn_get l] at he
  exact he.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun x _=>hc x) (Finset.mem_univ _)) (by positivity))
end YM.XSpace.Tide
