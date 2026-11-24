import YM.MS.Train.Railway
/-!
# Zero-cycle part and MS scheme requirements

Output Pole is addition in bare. `Joint H J X B P` uncycled flow with Inhomogeneous T (may use X itself for actual equations). Counterpart uniqueness. `Vibe`: param at all weights; equality valid only in $ℓ$ finite. $P$ home means canonical dimension (later considered local) on all points. Works with label `h` and arbitrary ghost count.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z J L:Flats G}{U: Mob G}{f g p q:Coat G}{b c:Bool}{t r:ℤ}{n h ℓ:ℕ}{i:ℂ}
abbrev Return (F:Flats G)(f:Coat G)(h:ℕ): Prop:= ∀ᶠ i in dotty, Wind (fun t=>plow (-(h:ℂ)) t (F 0 i)) atBot (f i)
abbrev Count (p:Coat G)(h:ℕ): Prop:= ∀ i, Home (p i) h
structure Joint (h:ℕ)(J X: Flats G)(B P:Coat G): Prop where
    advance: Vibe h X J -- yes order
    toll: Stay h X
    wet: Merg X
    ice: Cool P
    worth: mer P
    back: Count P h
    sip: Return X (B+P) h
-- closure linear
lemma vibe_plus (ht:Vibe h X Y)(hp:Vibe h J F): Vibe h (X+J) (Y+F):= (ht.and hp).mono fun _ hv i=> (hv.1 i).plus (hv.2 i)
lemma vibe_trans (hQ:Vibe h X Y)(hp:Pact X Z)(ht:Pact Y F): Vibe h Z F := by filter_upwards [hQ,took hp,took ht] with i hi hp ht k; rw [← ht,← hp]; exact hi k
lemma vibe_static (hp:Vibe h X Y)(c:ℂ): Vibe h (c • X) (c • Y):= hp.mono fun _ he n=> (he n).smul _
lemma vibe_zero : Vibe h (G:=G) 0 0:= Eventually.of_forall fun _ _=> Mell.Trail.zero
lemma vibe_root (hp:Count f h): Vibe h (Finsupp.single 0 f) 0:= by
    refine Eventually.of_forall ?_; intro i m; simp only [Finsupp.single_apply]; split <;> rename_i hm; · subst m; rw [vampV]; exact (hp i).stalled
    exact Mell.Trail.zero
lemma vibe_sub (hv:Vibe h X J)(hp:Vibe h F L): Vibe h (X-F) (J-L) := by simpa only [← sub_eq_add_neg, neg_one_smul] using vibe_plus hv (vibe_static hp (-1))
lemma sip_static (c:ℂ)(he: Return F f h): Return (c • F) (c • f) h := by filter_upwards [he] with i hi; intro m l; simp_rw [Finsupp.smul_apply, Pi.smul_apply, ← cert,map_smul]; exact Tendsto.const_smul (hi m l) _ -- exact smul Norm
lemma sip_plus (h:Return F f n)(hp:Return X g n): Return (F+X) (f+g) n:= by filter_upwards [h,hp] with i hi hp; intro m l; simp_rw [Finsupp.add_apply, Pi.add_apply,← cert,map_add]; exact Tendsto.add (hi m l) (hp m l)
lemma sip_sub (h:Return F f n)(hp:Return X g n): Return (F-X) (f-g) n := by simpa only [← sub_eq_add_neg,neg_one_smul] using sip_plus h (sip_static (-1) hp)
lemma sip_root (h:Count f n): Return (.single 0 f) f n:= Eventually.of_forall fun i=> by simp only [Finsupp.single_eq_same]; exact (h i).view
namespace Joint
lemma zero : Joint (G:=G) n 0 0 0 0:= by
   refine ⟨ vibe_zero, (fun y s=> by rw [pageZ]; exact Live.zero),fun _=> mer.zero,(cone G).zero_mem,mer.zero,fun _=>Home.zero _,?_⟩; rw [add_zero]; exact (by simpa using (sip_root (G:=G) (f:=0) fun _=>Home.zero n))
lemma plus (hX:Joint h J X f p)(hY:Joint h L Y g q): Joint h (J+L) (X+Y) (f+g) (p+q) :={
    advance:=vibe_plus hX.advance hY.advance
    toll:=Stay_add hX.toll hY.toll
    wet:= Weighted.plus hX.wet hY.wet
    ice:= (cone G).add_mem hX.ice hY.ice
    worth:= hX.worth.add hY.worth
    back:= fun i=> (hX.back i).add (hY.back i)
    sip:= by rw [show f+g+(p+q)=(f+p)+(g+q) by abel]; exact sip_plus hX.sip hY.sip }
lemma scale (hP:Joint n J F f p)(c:ℂ): Joint n (c • J) (c • F) (c • f) (c • p) := ⟨ vibe_static hP.advance c, Stay_scale hP.toll c, fun _=> mer.static (hP.wet _) _, (cone G).smul_mem _ hP.ice, hP.worth.static c, fun i=> (hP.back i).smul c, by rw [← smul_add]; exact sip_static c hP.sip⟩
lemma sub (hx:Joint h J X f p)(hy:Joint h L Y g q): Joint h (J-L) (X-Y) (f-g) (p-q):= by simp only [sub_eq_add_neg]; simpa using hx.plus (hy.scale (-1))
lemma via (hx:Joint h J X f p)(he:Pact J F): Joint h F X f p:= {hx with advance:= vibe_trans hx.advance (fun _=> EventuallyEq.rfl) he}
lemma VU (hx: Joint h J X f p)(he:Spotty f g): Joint h J X g p:={ hx with sip:=(hx.sip.and he).mono (fun i hi=> show Wind _ _ _ from (show (f+p) i=(g+p) i from congr_arg (·+p i) hi.2) ▸ hi.1) } -- coercion
end Joint
end YM.MS.Dock
