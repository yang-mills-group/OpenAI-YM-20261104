import YM.SchemeRG11.Flock.Feather
import YM.Pert.Lattice.Lifts
/-! Decoding the horizontal engineering leg by COLOR FREE linear pilot.
 Avoid assuming existence of color-equivariant splitting. -/
set_option maxHeartbeats 1500000
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Flock
open Function Lattice Pert Maxwell Tree Bark Pert.Bare Haze
variable {G:Gauge} {n:ℕ}
variable {E F:Type*}[AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F]
def plumage(f:Bevy ℝ)(c:E):Bevy E:=fun i x=>f i x • c
lemma gates (m:ℕ)(f:Bevy ℝ)(h:f∈team ℝ m)(c:E):plumage f c∈team E m:=team_linear ((LinearMap.id:Module.End ℝ ℝ).smulRight c) f m h
lemma stripes (f:Plane ℝ)(c:E)(s:Fliers) : fleet s (fun t=>f t • c)=fun t=> fleet s f t • c:=mule ..
lemma feather_b (f:Bevy ℝ)(c:E)(i j:Axis):bend (plumage f c) i j=fun x=> bend f i j x • c:=by funext x; simp only [bend,soar_apply,Pi.sub_apply,plumage, sub_smul]
def cloud (v:Feather n)(c:E):Bevy E:=plumage (finch v) c
abbrev Sky (G:Gauge)(n:ℕ):= Feather n × G.ColorIndex
def plume(v:Sky G n):=cloud v.1 (Maxwell.unitColor G v.2)
def plum {m:ℕ}(v:Feather m×G.ColorIndex): trunk G ℤ:= linkup (plume v)
def inkAge (v:Sky G n):= Flock.degree v.1
def lineP(v:Sky G n): Prop:= v.1.2.isLeft
lemma clouded (v:Sky G n): plume v∈team G.Color (inkAge v):=gates _ _ (finched _) _
lemma plunges (v:Sky G n)(he:¬lineP v): ∃ p:Plane G.Color, p∈ cap G.Color (inkAge v+1) ∧ lap p=0 ∧ incline p=plume v:=by
 obtain ⟨⟨a,i|i⟩,c⟩:=v
 · exact absurd (show lineP (⟨⟨a,Sum.inl i⟩,c⟩:Sky G n) from rfl) he
 let v:Plane ℝ:=vertPot i
 let Q:ℝ→ₗ[ℝ] G.Color:=(LinearMap.id:Module.End ℝ ℝ).smulRight (Maxwell.unitColor G c)
 let u:Sky G n:= ⟨⟨a,Sum.inr i⟩,c⟩
 have h:v∈cap ℝ (inkAge u+1):= (riseB _ i).property.1
 refine ⟨Q ∘ v,?_,?_,?_⟩
 · intro s hs; rw [plane_map, member.mp h _ hs]; exact funext fun _=>map_zero _
 · rw [lap_linear,show lap v=0 from (riseB _ i).property.2]; exact funext fun _=>map_zero _
 funext j; exact soaring_map ..
lemma up_zero (a:Plane G.Color) (j:ℕ)(x:Cover): wideLinear G j 1 x (linkup (incline a))=0:=by -- arbitrary
 have e: linkup (incline a)= ascent a:=rfl
 rw [e,← secular 1 x j (ascent a) (ascent a),sworn]

def reader(m:ℕ) :TurnArray m→ₗ[ℝ] (HIndex (m+1)→ℝ):=Classical.choose (pilot m)
def grove(m:ℕ) (k:HIndex (m+1)) (g:Labels.Taylor G m):G.Color:=WithLp.toLp 2 fun c=> reader m (fun i j v=> components g i j v c) k
lemma groove(m:ℕ) (j k:HIndex (m+1))(w:G.Color):grove m k (wideLinear G m 1 0 (linkup (plumage (hor j).val w)))=Pi.single (M:=fun _ => G.Color) j w k:=by
 ext l; let u:Bevy G.Color:=plumage (hor (m:=m+1) j).val w; have hu:u∈team G.Color (m+2):=gates _ _ (hor j).property w
 have ve (g : Labels.Taylor G m): WithLp.ofLp (grove m k g) l=reader m (fun i t v=> components g i t v l) k:=rfl
 rw [ve]
 have hh (i t:Axis)(v:Fin m→Axis): components (wideLinear G m 1 (0:Cover) (linkup u)) i t v l=w l* gauges m (transverse (m+1) j) i t v:=by
   rw [width u _ hu]; unfold components; rw [match_leg]; change leadT m u i t (basis ∘ v) l = _
   unfold leadT; rw [print_tip,show bend u i t=_ from feather_b (hor j).val w i t,stripes]; change (m.factorial:ℝ)⁻¹*(fleet (clutch v) (bend (hor j).val i t) 0 * w l)= _*( (m.factorial:ℝ)⁻¹ * fleet (clutch v) (bend (hor j).val i t) 0); ring
 rw [show (fun (i t:Axis) (v:Fin m→Axis)=> components (wideLinear G m 1 (0:Cover) (linkup u)) i t v l)=w l • gauges m (transverse _ j) from funext fun i=>funext fun t=> funext fun v=>hh i t v,map_smul,show reader m (gauges _ _)=Pi.single j 1 from Classical.choose_spec (pilot m) j]; by_cases he:j=k
 · subst k; simp
 simp [he]
lemma mass (m:ℕ)(s:TurnArray m→ₗ[ℝ]ℝ)(Q:Response G m)(L:G.Color→ₗ[ℝ] G.Color)(c:G.ColorIndex):
  L (WithLp.toLp 2 fun g=> s (fun a b i=> Q a b i g)) c = s (fun a b i=>L (Q a b i) c):=by
  conv_lhs=> rw [←Triangle.sum_color (G:=G) (WithLp.toLp 2 (fun g=> s (fun a b i=> Q a b i g)))]
  rw [map_sum]; simp only [map_smul,WithLp.ofLp_sum,smul_eq_mul, PiLp.smul_apply, Finset.sum_apply]
  rw [show (fun a b i=>L (Q a b i) c)=∑ d:G.ColorIndex,L (unitColor G d) c • (fun a b i=> Q a b i d) by
   funext a b i
   conv_lhs=> rw [←Triangle.sum_color (Q a b i)]
   simp only [Finset.sum_apply,map_sum,map_smul, WithLp.ofLp_sum,PiLp.smul_apply,Pi.smul_apply, smul_eq_mul]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..]
  rw [map_sum]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
lemma grove_star(m:ℕ)(k:HIndex (m+1))(g:Labels.Taylor G m)(u:G.El): grove m k (Labels.Taylor.paint u g)=G.adjoint u (grove m k g):=by
 ext c; exact (by
   let L : TurnArray m→ₗ[ℝ] ℝ:= LinearMap.proj k ∘ₗ reader m
   have H:= mass m L (components g) (G.adjoint u) c -- maybe G.adjoint is LIE linear eq
   unfold grove; rw [show components (Labels.Taylor.paint u g)=fun i j v=>G.adjoint u (components g i j v) from ?_] -- unfold grove
   exact H.symm
   unfold components; rw [Pert.RawLabels.takeCurl_color];rfl
   )
end YM.SchemeRG11.Flock
