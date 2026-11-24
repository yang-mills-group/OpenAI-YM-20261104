import YM.MS.Train.Dais
/-!
# Operations preserve strong Fine at appropriate assignments
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{K L E:Mob G}{f g:Coat G}{b c:Bool}{t q m:ℤ}{U V:Rip G}{k n h ℓ:ℕ}{i:ℂ}{s:ℝ}
structure Fine (b:Bool) (i:ℤ) (F:Coat G): Prop where
   tune: Sun b F
   ghost: To F (collar i G)
   sense: realAlong F (sight G)
namespace Fine
lemma zero : Fine b t (0:Coat G):= ⟨Sun.zero, (washed (collar ..)).zero,(real_axis (sight G)).zero⟩ -- implicit
lemma add (h:Fine b t f)(he:Fine b t g) : Fine b t (f+g):= ⟨h.tune.add he.tune, (washed _).add _ _ h.ghost he.ghost,( real_axis _).add _ _ h.sense he.sense⟩
lemma smul (h:Fine b t f)(hx:star i=i): Fine b t (i • f):= ⟨h.tune.smul _,h.ghost.mono fun _ hv=> (collar t G).smul_mem _ hv, (show realAlong _ _ from Eventually.mono h.sense (fun _ hp=> re_part _ hx _ hp))⟩
lemma neg (h:Fine b t f): Fine b t (-f):= by simpa only [neg_one_smul] using h.smul (i:=(-1)) (by simp)
lemma sub (h:Fine b t f)(he:Fine b t g): Fine b t (f-g):= by rw [sub_eq_add_neg]; exact h.add he.neg
lemma tire (h:Fine true t f): Fine false t f:=⟨h.tune.tofalse, h.ghost,h.sense⟩
lemma alter (h:Fine b t f)(he:Spotty f g): Fine b t g:= by
   refine ⟨ h.tune.congr he, (h.ghost.and he).mono fun i h=>h.2 ▸ h.1,?_⟩; unfold realAlong; filter_upwards [( show ∀ᶠ i:ℝ in realDotty, f i∈ sight G from h.sense),dotty_touch.eventually he] with p hp hx; rw [← hx]; exact hp
lemma HeapF : Heap (Fine (G:=G) b t):= ⟨ zero, fun _ _=>add⟩
lemma wood (h:Fine b t f)(hp: Fine b q g)(hv:Knot b U)(hc:closedF U c)(ht:veil U)(hy:ReadyG U)(hx:reverseF U)(hH:Credit m U): Fine b (t+q+m) (tapeB (squad U) f g) := by
   refine ⟨ h.tune.tree hp.tune hx hv hc,?_,?_⟩
   · filter_upwards [h.ghost,hp.ghost] with p hf H; replace hf: Collar t _:= hf; replace H: Collar q _:= H; exact ⟨sym_tree hf.sym H.sym hc, tree_hues hf.color hy H.color hc,Occup hf.ghost H.ghost hH hx ⟩
   exact ( Eventually.and h.sense hp.sense).mono fun i h=> spotlight h.1 h.2 ht hx
lemma eye (h:Fine b t f)(hp:Knot b U)(ht: veil U)(hx:ReadyG U)(he:Credit m U): Fine b (t+m) (swamp U f):= by
   refine ⟨ swamp_m h.tune hp,?_,?_⟩; · filter_upwards [high0,sunny h.tune,h.ghost] with i hi hT hf; replace hf: Collar t _:= hf; rw [swamp_spec hp hT hi]; exact (collar _ G).smul_mem _ (show Collar (t+m) _ from ⟨sym_strand hf.sym hT hp hi,scenery hf.color hx hT hp hi,ghost_l t m hf.ghost he hT hp hi⟩)
   unfold realAlong; filter_upwards [dotty_touch.eventually ( sunny h.tune), dotty_touch high0, (show ∀ᶠ i:ℝ in realDotty,f i∈sight G from h.sense)] with i hi hI hx; rw [swamp_spec hp hi hI]; exact re_part _ (fee_real _ (by simp)) _ ( featured ht hx hi hp i ) -- arguments order
end Fine
abbrev Blazing (b:Bool)(t:ℤ)(F:Flats G):= SeedP (Fine b t) F
-- declare actual uses for t/h. cannot apply field aliases.
lemma chair_a (A:ℝ) : ReadyG (A0 G A):= fun _=> rainbow G ( Landau.line (exp A))
lemma c_bo (t:ℝ){b:Bool}: Knot b (A0 G t):= by cases b; exact ( A_caps G t).clearer; exact A_caps G t
lemma blazeG (h:Blazing b t F): Blazing b t (CycleN (A0 G s) F):= by
   refine Fine.HeapF.pipe _ _ _ (fun i=>?_); convert! (h i).eye (c_bo s) (voile_a G s) (chair_a s) (kred G s) using 1; omega
lemma blazeB (h:Blazing b t F)(ht:Blazing b q X): Blazing b (t+q) (TreeN (A0 G s) F X):= by
   refine Fine.HeapF.explo _ F X (fun i j=>?_); obtain hz := (h i).wood (ht j) (c_bo s) (cl_a G s) (voile_a G s) (chair_a s) (reverse_a G s) (kred G s); simpa only [add_zero] using hz -- ζ
end YM.MS.Train
