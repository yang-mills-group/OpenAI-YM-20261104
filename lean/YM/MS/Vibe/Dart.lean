import YM.MS.Vibe.Morse
/-!
# Horizon dynamics at complex ε

Ext.P Rotation. Evanescent data always entering master expression.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
lemma curveV (hp: Moony b J)(hx: Vibe h J L): ∀ᶠ i in dotty,∀ t y, Curve (fun s=> Parade J h y s i) ( Parade L h y t i) t:= by
   filter_upwards [ Moony.sunup hp,hx] with i hi hx s y; simp_rw [Page (J.support∪L.support) Finset.subset_union_left,Page (J.support∪L.support) Finset.subset_union_right] -- unification simp risk
   let S:=J.support∪ L.support; let V(j:ℕ)(s:ℝ):= hikeP i h j y s (J j i); let T(j):=hikeP i h j y s ( L j i); simp_rw [Finset.sum_apply]; convert! Curve.sum S (u:=V) (Y:=T) (fun j hj=> ?_) using 1; · ext; unfold V; simp [S,Finset.sum_apply]
   exact Curve.scale (Pearl.weight ..) ( horizonP (vamp i h j) (hi j).price ( hx j |>.derive s)) -- T type
structure Sip (i:ℂ)(X Y:ℝ→ℝ→ T (Mob G))(n:ℕ)(k:ℤ): Prop where -- X(y,s)
   food s y : Form0 false (X s y n)
   mold s y : Collar k (X s y n)
   myst s y : Form0 false (Y s y n)
   head s y : Curve (fun s=> X s y n) (Y s y n) s
abbrev script (c:ℂ)(h:ℕ)(X:T ( Flats G)): ℝ→ℝ→ T (Mob G) := fun s y=> File c s y h X
lemma ofG (h:Gang b n t J): ∀ᶠ i in dotty, ∀ s y, Collar t (Parade J n y s i):= by
   obtain ⟨r,hr⟩:= h.price; filter_upwards [facade J (P:=fun _ _ X=>Collar t X) id dotty (fun _ _=> (collar t G).zero_mem) (fun i=> (hr i).fine.ghost)] with i hi t y; refine ?_; unfold Parade Finsupp.sum; exact (collar _ _).sum_mem fun j hj=> (collar _ _).smul_mem _ (need_col.seo (hi j) _ _) -- t shadows Int remove
lemma grew_host (h:∀ i,Host (X i) 4)(hv:∀ i,Host (F i) m)(n:ℕ): Host (pairW (drive0 G) X F n) m:= Host.sum (antidiagonal n) (fun i _=> Host.tree (h _) (hv _) (reverse_a G 0) (c_bo 0) (cl_a G 0) (x:=4) (by push_cast; ring))
lemma grow_host (hp:leader G X f g) (n:ℕ): Host (program G n X+step0 G (X n)) 4:= by
    have ht(i:ℕ):= Host.host ( gang (hp i)); rw [ pc_max ((hp 0).2 rfl) n]; exact ((grew_host ht ht n).smul _).plus (ht n).core
lemma leaf (hp:leader G X f g)(n:ℕ): ∀ᶠ i in dotty,Sip i (script i 4 X) (fun s y=> ( Grid i y s G ).grow (File i s y 4 X)) n 0 := by
    obtain ⟨r,H0,H,hY⟩:= (hp n).1; let F := program G n X+step0 G (X n); obtain hv:Moony true (X n):=clockMoon H; have hK:= Moony.toss hv;
    filter_upwards [growthB hK ((hp 0).2 rfl), Moony.march hK 4, ofG (gang (hp n)),Moony.march (grow_host hp n).bill 4,curveV hK H0.advance] with i hi hE hz hL ht; refine ⟨ fun s y=>hE y s, hz,fun s y=>?_,fun s y=>?_⟩; rw [← hi]; exact hL y s; rw [← hi]; exact ht s y
lemma mark_h (hp:leader G X f g)(he:comet h t X q F p)(n:ℕ): Host (platform X n F+step0 G (F n)) h:= by
    have ht (i:ℕ):=Host.host (gang (he i)); rw [ pm_max ((hp 0).2 rfl)]; exact ( grew_host (fun i=>Host.host (gang (hp i))) ht n).plus (ht n).core
lemma aerial (hp:leader G X f g)(he: comet h t X q F p)(n:ℕ): ∀ᶠ i in dotty,Sip i (script i h F) (fun s y=> ( Grid i y s G).lives (File i s y 4 X) (File i s y h F)) n t:= by
    obtain ⟨r,H0,H,hY⟩:= (he n).1; obtain hv:Moony false (F n):= clockMoon H; filter_upwards [growthM hv ((hp 0).2 rfl) h, Moony.march hv h, ofG ( gang (he n)), Moony.march ( mark_h hp he n).bill h, curveV hv H0.advance] with i hi hX hk hV ht; refine ⟨ fun s y=>hX y s,hk, fun s y=>?_,fun s y=>?_⟩; rw [← hi]; exact hV y s; rw [← hi]; exact ht s y
end YM.MS.Emit
