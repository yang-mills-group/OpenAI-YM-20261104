import YM.FVA2.Lambda.TokenS
import YM.FVA2.Lambda.Capture
/-!
# Pull derivatives through ∫ p with supplied PlanetD fixed-scale Majorant

 Constant local part not determined and cancels only after ∂ ext-momentum.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Pages
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect MS.Latch MS.Latch.Job
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open MS.Osc MS.Osc.Snap MS.Breeze
open Canvas (quad high top_quad line4 triple upperquad trigger thermal₂)
open Area Shells
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{s t:ℝ}
local notation "g"=>triple G
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
variable (D E:ℝ→ℝ)(q:QP)(i j k l:G.ColorIndex)(a b:BH G)(p:QP)(w r:List (Lane4 G))(F:Law G)(m n:ℕ)
abbrev pairL (a b:BH G)(p:QP): List (Lane4 G):= [(a,p),(b,-p)]
abbrev μq:= covMeasure Axis
lemma sponge {A:Type*}[MeasurableSpace A] (μ:Measure A) {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] {f:A→ℝ→E}(h:Majorant μ f)(n:ℕ): ((Nat.factorial n:ℝ)⁻¹ • iteratedDeriv n (fun x=>∫ a,f a x∂μ) 0)= ∫ a,(Nat.factorial n:ℝ)⁻¹ • iteratedDeriv n (f a) 0 ∂μ:= by
    simp_rw [iteratedDeriv_eq_iteratedFDeriv]; rw [h.identity, ContinuousMultilinearMap.integral_apply (h.integ ..), integral_smul ]
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
include hm
lemma credit {n:ℕ}: high X n (s,t)∈ Breeze.Wallet G:= by
   apply Breeze.permits.mpr; intro E _ _ w; rw [Breeze.spaceArc]; refine Outlook.BigG (hp:=( blade0 (s:=t) ( y:=s) ( Host.host ( gang ( hm n ) ) ) ).price ) 0 w
lemma under (n:ℕ)(l: Plane.Wire (BH G) ℝ QP): Majorant μq (fun q x=> trc (line4 G (hot t)) q ( high X n (s,t)) (sail l x)):= by
   rw [show line4 G ( hot t )= Rake.PlanetD G t from (Shells.sweep G t).symm ]; let Z:= Job.single Unit; have hp := credit (n:=n) (t:=t) (s:=s) hm; have hw:= Latch.topCycle (w:=l) ( Latch.Lease.highp ( show Latch.Lease false false Z (fun _=> high X n (s,t)) 1 from hp)) (Breeze.SheetU t) (fun i=> Bool.noConfusion i) (fun _=>zero_le_one) (fun _=>zero_le_one)
   exact MS.Rapid.major ( Reserve.cover (S:=Z) (μ:=μq) ( Module.finrank ℝ QP + 1 ) (by unfold QP; omega) ) hw ()
lemma no_pair (p:QP): quad G D ( high X 1 (s,t) ) ( high X 1 (s,t) ) ( pairL a b p )=0:= by
    let F:= high X 1 (s,t); have he(l m:Lane4 G): F [l,m]=0:= (Canvas.opens hm (s,t) ([l,m]) (by simp)).trans (Slice.trank _ (by simp))
    have h' (i:Lane4 G)(w:List (Lane4 G)): Bead.attach D F F [i] w=0:= by unfold Bead.attach Bead.summit; simp [ he ]
    rw [Bead.A_quad]; change scatter Ψ (pairL a b p) ( Bead.attach D F F )=_; have hp : net ( pairL a b p)=0:= by simp [pairL,net]
    have hf(w): Bead.attach D F F [(a,p),(b,-p)] w=0:= Bead.a_guard (l:=pairL a b p) D F F hp
    simp only [ pairL,scatter_cons,scatter_nil, h', hf, Bead.a_guard (l:=[]) D F F rfl, add_zero, mul_zero ]
lemma two (n:ℕ) : torch n ( trigger X 2 (s,t) ) ( pairL a b p )= ∫ q : QP, reading n (fun x:ℝ=> Flux.trc (line4 G ( hot t )) q (high X 2 (s,t) ) (pairL a b (x • p))) ∂μq:= by
    let w:=pairL a b p; let V(x:ℝ):= pairL a b (x • p); have hx(x:ℝ): sail (ray w) x=V x:= by simp [w,pairL, V];
    rw [ torch_at ]; change reading n (fun x:ℝ=> trigger X 2 (s,t) (sail (ray w) x))=_ ; simp_rw [ hx, thermal₂ ]; dsimp only [V]; simp_rw [ no_pair (hot t) a b hm, add_zero ];
    have hu: Majorant μq ( fun q (x:ℝ)=> Flux.trc (line4 G ( hot t )) q ( high X 2 (s,t) ) ( V x )):= by obtain hv:= under (s:=s) (t:=t) hm 2 (ray w); simp_rw [hx] at hv; exact hv
    exact sponge μq hu n
lemma head_when (k:QP): trc ( line4 G D ) q ( high X 2 (s,t) ) ( pairL a b k )= trc ( line4 G D ) q ( ( high X 2 (s,t) )∘ Canvas.onset ) ( pairL a b p ) + trc ( line4 G D ) q (quad G (melt t) g g) ( pairL a b k ):= by
    rw [at_trc,at_trc, at_trc]; simp only [← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=> ?_; rw [ Canvas.upperquad hm _ _ _ rfl (fun _=>by simp [pairL,net]) ]; simp [mul_add, pairL, Canvas.onset ]
lemma skip {v:ℕ}(hV:0<v): reading v (fun x:ℝ=> Flux.trc (line4 G ( hot t )) q ( high X 2 (s,t) ) ( pairL a b (x • p)))= reading v (fun x:ℝ=> Flux.trc ( line4 G ( hot t )) q ( quad G ( melt t ) g g ) ( pairL a b (x • p))) := by
    simp_rw [ head_when ( hot t ) q a b (0:QP) hm ]; unfold reading; rw [iteratedDeriv_const_add hV]
lemma pair (n:ℕ)(hV:0<n): torch n ( trigger X 2 (s,t) ) ( pairL a b p )= ∫ q:QP, reading n (fun x:ℝ=> Flux.trc (line4 G (hot t)) q ( quad G (melt t) g g ) (pairL a b (x • p))) ∂μq:= by rw [two a b p hm]; simp_rw [ Pages.skip _ _ _ _ hm hV ]
end YM.FVA2.Lambda.Pages
