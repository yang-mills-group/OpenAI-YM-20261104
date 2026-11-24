import YM.FVA2.Lambda.Hard
/-!
# Compute high rank4 at d=4, n=2. Local ambiguity constants not evaluated

 Rank4 φ⁴ only survive through constant. No assertion of measured heat formula at all-zero volume or analytic connection assumptions. Inputs `leader` recursion & smoothness exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Canvas
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City MS.Book.Program MS.Logarithm MS.High.Knobs
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:ℕ}
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
local notation "Ψ"=>field ( parity (A:=Axis) (C:=G.ColorIndex) )
abbrev line4 (G:Gauge)(D:ℝ→ℝ): Latch.Edge G:= Shells.link G D
abbrev triple (G:Gauge) : Law G:= pulseX G 1 0
def quad (G:Gauge)(D:ℝ→ℝ)(F H:Law G) : Law G:= ((2:ℂ)⁻¹) • Flux.tree parity ( line4 G D ) F H
open Shells (hot melt)
variable (D:ℝ→ℝ)(F H:Law G)(w:List (Lane4 G))(x t:ℝ)
lemma regression {f:ℝ→ℂ}(h:∀ t, HasDerivAt f 0 t)(hu:Tendsto f atBot (𝓝 0)): f t=0:= by rw [Wind.constancy h]; refine tendsto_nhds_unique ?_ hu; exact tendsto_const_nhds.congr (fun i=> (Wind.constancy h i).symm)
lemma on_tree (G:Gauge)(u:ℝ→ℝ)(F H:Law G)(w:List (Lane4 G)): quad G u F H (onset w)=0:= by
   unfold quad Flux.tree; rw [Pi.smul_apply, onset, sail_scatter]; suffices hP: scatter ( field ( parity (C:=G.ColorIndex) (A:=Axis) ) ) (ray w) (fun x y=> Flux.attaches parity ( line4 G u ) F H (sail x 0) (sail y 0))=0 by rw [hP,smul_zero]
   refine Eq.trans (scatter_congr ( field ( parity (C:=G.ColorIndex) (A:=Axis) ) ) _ _ (fun _ _=>0) (fun l r _=>?_)) ( map_zero ( allocate .. )); simp [Flux.attaches,sail_net,line4,Shells.z]
lemma re_pair : HasDerivAt (fun t:ℝ=> quad G (melt t) F H w) (quad G (hot t) F H w) t:= by
    have hj(f:Law G): Heat.Zip (fun _=> f) 0 t:= fun _=> hasDerivAt_const .. ; obtain hp:= tree_zip (fun s=> Shells.flipped G ( melt s )) ( Shells.flipped G ( hot t ) ) ( Shells.levy G t ) (hj F) (hj H) w
    rw [ show Flux.tree _ (Shells.link G (melt t)) 0 H=0 from (show boulevard parity _ 0 H=0 from by rw [map_zero]; rfl), show Flux.tree _ (Shells.link G (melt t)) F 0=0 from map_zero (boulevard parity _ F), add_zero,add_zero ] at hp; exact hp.const_mul _
lemma pair_bot : Tendsto (fun s=> quad G (melt s) F H w) atBot (𝓝 0):= by
    let L s:= line4 G ( melt s ); have hc (l r): Tendsto (fun s=> Flux.attaches parity ( L s ) F H l r) atBot (𝓝 0):= by
        dsimp only [L,line4]; simp_rw [ Heat.convertR (F:=F) (H:=H) ( Shells.flipped G ( melt _ )) ];
        have h₀ (i j:BH G): Tendsto (fun s=> Heat.radius parity ( L s ) i j F H l r) atBot (𝓝 0):= by obtain he:= ( ( ( Shells.xray i j (-net l) ).const_mul (2:ℂ) ).mul_const (cross (parity j) (degree Ψ l) * F ((i,-net l)::l))).mul_const ( H ((j,- -net l)::r) ); simp only [mul_zero,zero_mul] at he; exact he
        simpa only [Finset.sum_const_zero] using tendsto_finsetSum univ (fun i _=> tendsto_finsetSum univ (fun j _=> h₀ i j))
    have hg (T:ℝ→ Shared (Lane4 G) ℂ)(W:Shared (Lane4 G) ℂ)(he:∀ i j, Tendsto (fun s=> T s i j) atBot (𝓝 ( W i j ))): Tendsto (fun x=> scatter Ψ w ( T x )) atBot (𝓝 (scatter Ψ w W)):= by induction w generalizing T W with | nil=> exact he [] []| cons i w ih=> exact ih _ _ (fun i j=> (he _ _).add (( he _ _ ).const_mul _) )
    obtain hP := (hg (fun s=> Flux.attaches parity ( L s ) F H ) 0 hc); rw [ show scatter _ w 0=(0:ℂ) from map_zero (allocate Ψ w) ] at hP; apply ( (show ((2:ℂ)⁻¹) * 0=0 from mul_zero _) ▸ hP.const_mul ((2:ℂ)⁻¹) ) -- rewrite
lemma thermal₂ : trigger X 2 (x,t) w= Flux.cycle (line4 G (hot t)) ((spaceD G).measure) (high X 2 (x,t)) w + quad G (hot t) (high X 1 (x,t)) (high X 1 (x,t)) w:= by
  simp only [trigger,Domain.recu,Domain.using_tree, Pi.add_apply, Shells.sweep, show Domain.paths 2 1={1} from rfl, Finset.sum_singleton]; rfl
lemma thermal₃ : trigger X 3 (x,t) w= Flux.cycle (line4 G (hot t)) ((spaceD G).measure) (high X 3 (x,t)) w +( quad G (hot t) (high X 2 (x,t)) (high X 1 (x,t)) w + quad G (hot t) (high X 1 (x,t)) (high X 2 (x,t)) w ):= by
   rw [trigger,Domain.recu,Domain.using_tree,show Domain.paths 3 1={1,2} from rfl, Finset.sum_pair (by decide), smul_add,Pi.add_apply, Pi.add_apply, Shells.sweep ]; rfl -- sweep
include hm
lemma cycle0 (hV:n<w.length): Flux.cycle (line4 G D) (spaceD G).measure (high X n (x,t)) w=0:= Latch.capcy (fromD hm n x t) _ _ w (by omega)
variable (hr:w.length=4)
include hr
lemma top_quad : quad G D (high X 1 (x,t)) (high X 1 (x,t)) w= quad G D (triple G) (triple G) w:= by
   have hr0: Limit ( high X 1 (x,t) ) 3:= fromD hm 1 x t; have hr':Limit (triple G) 3 := ( fund_one G 0 ).up
   unfold quad Flux.tree; simp only [Pi.smul_apply]; congr 1; apply scatter_congr; intro l r h; simp_rw [convertR (F:=high X 1 _) (H:=high X 1 _) (Shells.flipped G D), convertR (F:=triple G) (H:=triple G) ( Shells.flipped G D )]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold radius; dsimp only; obtain he:= split_length h; rcases lt_trichotomy 2 l.length with h|h|h
   · rw [ hr0 ((i,-net l)::l) (by simp; omega), hr' ((i,-net l)::l) (by simp; omega) ]; simp
   · unfold high triple; rw [ opens hm _ ((i,-net l)::l) (by simp; omega), opens hm _ ((j,- -net l)::r) (by simp; omega) ];
   rw [hr0 ((j,- -net l)::r) (by simp; omega),hr' ((j,- -net l)::r) (by simp; omega) ]; simp
lemma top_der (hc:Course true w): HasDerivAt (fun t=> high X 2 (x,t) w) (quad G (hot t) (triple G) (triple G) w) t:= by obtain hv := steam hm (n:=2) x hc (by omega) (by decide) t; rw [thermal₂, cycle0 hm _ _ _ _ (by omega),zero_add, top_quad hm _ w _ _ hr ] at hv; exact hv
lemma no_origin_t : HasDerivAt (fun t:ℝ=> high X 2 (x,t) ( onset w )) 0 t:= by obtain he:= top_der hm ( onset w ) x t (by rwa [on_len]) (closed_onset w); rw [on_tree G] at he; exact he
lemma not_marginal (hv:4<fieldDim wfield w): high X 2 (x,t) ( onset w )=0:= by apply regression ( f:=fun t=> high X 2 (x,t) (onset w) ) t (fun t=> no_origin_t hm w x t hr); apply down hm x (closed_onset w) (by rw [on_len]; omega) (by decide) ; rwa [on_mass]
/-- Top rank, closed, n2, high(X) value local term + treeH BV₁². -/
lemma upperquad (hc: Course true w): high X 2 (x,t) w= high X 2 (x,t) ( onset w ) + quad G ( melt t ) (triple G) (triple G) w:= by
    let f(t:ℝ):= high X 2 (x,t) w -high X 2 (x,t) (onset w) - quad G ( melt t ) (triple G) (triple G) w
    have ht(s:ℝ): HasDerivAt f 0 s:= by convert! (((top_der hm w x s hr hc).fun_sub ( no_origin_t hm w x s hr )).fun_sub ( re_pair (triple G) (triple G) w s )) using 1; abel
    have hd:= fringes hm (n:=2) x hc (by omega) (by decide) (by have h₀:= length_pay w; omega); obtain he := regression t ht (show Tendsto f atBot (𝓝 0) by simpa only [sub_self] using hd.sub (pair_bot (triple G) (triple G) w)); exact Eq.trans (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)) (add_comm ..)
end YM.FVA2.Lambda.Canvas
