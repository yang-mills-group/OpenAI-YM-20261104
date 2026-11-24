import YM.X.Fill.Dog
/-!
# one cross between mark-Heated and V, Ward terms at volume: released contributions directly by IBP. Local measure. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt Shelf Size Print Crystal
open Ocean Plate
open Stems hiding X
open scoped Topology ContDiff Classical BigOperators
variable {q:ℕ+}(hq:1<q.val){R:ℝ}{b:Bool}{r:ℝ}{k m n:ℕ}{a p:ℤ}{G:Gauge}
variable {P S: Deck G}{A:ℕ→Brush G} (h:Tide q r A)
include hq h
lemma seed_one (hp:Dog q G r false a P)(f:Fan G)(hf:f∈Reed.grads G k): exitP A (Clove.ann q true f P)∈ seed q r (a+(k+1:ℕ)):= by
   induction hp with
   | @sky x y hx=>
        rw [show ann q true f (glass y)=0 from ?_,show exitP A 0=0 from ?_]; exact Submodule.zero_mem _
        · ext1;ext1;simp [exitP]
        ext1;ext1;simp [ann, glass,edge,slit_C]
   | pet g m hm=> rw [ann_letter,exit_sky]; let B(n:Side)(x y:Cover):= spend n x y g f; change squall q B∈_; have hp:= enrolled₂ g f hm hf; rw [← one_mul (squall q B)]; exact seeded B _ (k:=m+k) hp (Chase.falls hq (show Chase q r 0 (1:Mist ℂ) from Chase.quiet (1:ℂ)) (by omega))
   | @prod a b P S t u hT hU=> rw [ann_mul,exit_add,exit_mul,exit_mul, mul_comm (exitP A P), mul_comm (exitP A S)]; apply Submodule.add_mem
                               · exact fewer hq (fed hq hU (t.prism hq h)) (by omega);
                               exact fewer hq (fed hq hT (u.prism hq h)) (by omega)
   | plus x y h₀ h₁=> rw [ann_add,exit_add];exact Submodule.add_mem _ h₀ h₁
   | moves _ h t=> exact fewer hq t (by omega)
lemma seed_hit (hp:Dog q G r false a P)(hb:Dog q G r true p S): exitP A (purseK q P S)∈ seed q r (a+p):= by
   induction hb with
   | sky h'=>rw [glass_hit,show exitP A 0=0 from ?_]; exact Submodule.zero_mem _; ext1;ext1;simp[exitP]
   | pet f k he=> rw [show purseK q P (Clove.fresh true f)=ann q true f P from funext (fun i=>funext fun z=> hit_glyph ..)]; exact seed_one hq h hp f he
   | @prod a' n f g hF hG x y=>
       rw [show purseK q P (f*g)=f * purseK q P g + g* purseK q P f from funext (fun i=>funext fun z=> Derivation.leibniz ..), exit_add,exit_mul,exit_mul, mul_comm (exitP A f),mul_comm (exitP A g)]; exact Submodule.add_mem _ (fewer hq (fed hq y (hF.prism hq h)) (by omega)) (fewer hq (fed hq x (hG.prism hq h)) (by omega))
   | @plus a x y h' p u v=> rw [show purseK q P (x+y)= purseK q P x+purseK q P y from ?_,exit_add]; exact Submodule.add_mem _ u v; ext1 i; ext1 z; unfold purseK; simp only [Pi.add_apply,map_add]
   | moves p h u=> exact fewer hq u (by omega)
lemma horizon_v (F:Word G): Dog q G r true 4 (∑ i:PlaqAxes,floatP true (vertex i)):= Dog.fs _ fun _ _=> Dog.trail (fire_verse _)
variable {F: Labels.Frames G} (s:Bare.Shop F)(χ: Floor R)(W: Word G)
omit hq h in
lemma hollow_v (q:ℕ+)(F:Word G)(χ:Floor R)(i:ℕ): hollow q F χ i= fireMask (Floor.maskL q χ i):=rfl
-- glint directly evaluated as sphere aperture at zero and ∆single. Scale license.
lemma glitter (hp:R<r) : Released (fun i=> snap (A i) (glint q W χ i)):= by
    let tT(k):= (Floor.maskL q χ k); let f:Deck G:=fun i _=> load q W i; let g:= ∑ i:PlaqAxes,floatP true (vertex (G:=G) i); let v(i:ℕ):=(epsilon q i ^(-(W.d:ℤ))); let b:= Once fun i:ℕ=>Complex.ofReal (v i); let w:= W.d
    have hv : Chase q r (-(w:ℤ)) b:= Chase.com (Chase.power _) -- real alter lift
    have hu(i:ℕ) : hollow q W χ i= beadR (tT i) (g i):= by rw [hollow_v,fireMask]; apply congr_arg; ext1 z; unfold g; simp_rw [Finset.sum_apply,dress_fire];rfl
    let p:= purseK q f g; let L (i:ℕ):= (LinearMap.mulLeft ℂ (load q W i)).restrictScalars ℝ; let M(i:ℕ):= ((hit (flow G (side q i)) (load q W i)).toLinearMap).restrictScalars ℝ; let e:= exitP A p; let B:= exitP A (f*g);
    have he(i:ℕ): snap (A i) (glint q W χ i)= influx tT (B*b) i + influx tT (e*b) i:= by
       let Y:= v i • ((snap (A i)).toLinearMap.restrictScalars ℝ); have h₁ (p:Curly G):Y p= b i 0 * snap (A i) p:= by exact Complex.real_smul ..
       unfold glint; rw [hu]; change snap (A i) (_ • (L i (beadR (tT i) (g i)) + M i (beadR (tT i) (g i))))=_; rw [show snap (A i) ((epsilon q i)^(-(W.d:ℤ)) • _) = Y (L i (beadR (tT i) (g i))+ M i (beadR (tT i) (g i))) from map_smul ((snap (A i)).toLinearMap.restrictScalars ℝ) ..,map_add];
       change (Y.comp (L i)) _+ (Y.comp (M i)) _ = _; rw [beadLm,beadLm]; apply congr_arg₂ _; unfold influx; refine congr_arg _ ?_; ext1 z; change Y (load q W i * g i z)= snap (A i) (load q W i * g i z)*b i 0; rw [h₁, mul_comm]
       unfold influx; refine congr_arg _ ?_; ext1 z; change Y (p i z)= snap (A i) (p i z)* b i 0;rw [h₁, mul_comm]
    have hx : Dog q G r false w f:= Dog.forever hq W; have hy: Dog q G r true 4 g := horizon_v hq h W
    have hB : Chase q r ((w+4:ℤ)+(-(w:ℤ))) (B*b):= by unfold B; rw [exit_mul]; exact Chase.mulC hq (Chase.mulC hq (hx.prism hq h) (hy.prism hq h)) hv
    simp_rw [he]; exact Released.add (mask_won hq χ (hB.visa χ.positive.le hp) (by omega) (by omega)) (seed_rise hq χ hp (fewer hq (fed hq (seed_hit hq h hx hy) hv) (by omega)))
omit h in
lemma warm_apt (hp:R<r) : Apt q r (warm q s W χ) := by
    refine ⟨Wide.sense W χ s q,fun A h=>?_⟩; unfold warm; simp_rw [map_sub]; exact Released.sub (Gravity.ripe hq s W χ hp h) (glitter hq h χ W hp)
end YM.PositionX.Friend
