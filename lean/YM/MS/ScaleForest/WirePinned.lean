import YM.MS.ScaleForest.LinearSweep
/-!
# Between-pin sweep of a forest (also one with a proper Laurent pole)

The CARPET integrates momentum, with rephasings from the separated pins, and the dimensional
read uses the whole external axis through them.
`placedEq` derives the agreement of the signed between-pin integral (sum over the
contractions) with an alternative recipe using the same cycle operation
as for unmarked kernels, when using sturdy, kPrice children at the current regulator. A
price/oscillatory estimate in `WaveSwipe`, needed for performing the scale
integrals before specialization, will use the same measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Fiddle
open scoped Topology ContDiff
variable {G : Gauge} {s : ℂ} {K : Rip G} {X Y : Mob G} {m n : ℕ} {I E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutWing (K : Rip G) (X Y : Mob G) (W : Touch G m E) : (SectorP m×ℝ)×E→ℂ:= fun p=>
   symmetricCut K X Y (slideA (Nat.lt_succ_self m) p.1) (Arts.lift (Nat.le_succ m) (sail W p.2))

/-- Measure matches closing a loop. -/
def pinned (K : Rip G) (s : ℂ) (y : ℝ) (A : QP) (X Y : Mob G) : Mob G :=
   fun m w=> tenorK s y • swoop s (Px m) m (cutWing K (rephase A X) Y (ray w)) (1:ℝ)

def sweptRef (z : ℂ) (K : Rip G) (X Y : Mob G) : Mob G := ocean z K (weave X Y) - weave (ocean z K X) Y - weave X (ocean z K Y)

private def Lfac (z:ℂ)(K : Rip G)(X Y : Mob G)(l r : Touch G m E) := factors (fieldVal (Y m) r) (wing z K X l)
private def Rfac (z:ℂ)(K : Rip G)(X Y : Mob G)(l r : Touch G m E) := factors (fieldVal (X m) l) (wing z K Y r)
private def μ_tree (W : Touch G m E) (f : Touch G m E→Touch G m E→ (SectorP m×ℝ)×E→ℂ) := SweepScat (field Landau.parity) W f

variable (W : Touch G m E) (h : Knot false K) (he : closedF K false) (ht : reverseF K)
   (hx : Form0 false X) (hy : Form0 false Y) (hs : s∈Town)
include h hx hy
include he ht in
theorem cut_projection (s : ℂ) : cutWing K X Y W= wing s K (weave X Y) W-μ_tree W (Lfac s K X Y)-μ_tree W (Rfac s K X Y) := by
   funext ⟨p,x⟩; unfold cutWing; rw [← z_cross he ht X Y _ hx.token hy.token h.token s]
   unfold references μ_tree SweepScat Lfac Rfac wing; simp only [factors, Pi.sub_apply,fieldVal,
     scattered,scatter_up,sail_scatter,hx.token.grows,hy.token.grows];
   simp_rw [mul_comm (X m _)];

omit hy in
private theorem sweepSelf [FiniteDimensional ℝ E] (z : ℂ): Sweeping (wing z K X W):= ⟨exact_test hx.price h.price W z,wing_mirror hx.token h.token z W⟩

variable [FiniteDimensional ℝ E]
include he ht in
theorem cutSweep : Sweeping (cutWing K X Y W) := by
   rw [cut_projection W h he ht hx hy 0]
   exact Sweep_sub (Sweep_sub (sweepSelf W h (form_weave hx hy) _)
     (Sweep_gathers (field parity) W (Lfac 0 K X Y) (fun l r _=> Sweep_mult _ (hy.price m E r) (sweepSelf l h hx _))))
     (Sweep_gathers (field parity) W (Rfac 0 K X Y) (fun l r _=> Sweep_mult _ (hx.price m E l) (sweepSelf r h hy _)))

include he ht hs

theorem pinnedIntegrates (A : QP) : let f:=cutWing K (rephase A X) Y W
    (∀ r : ℝ×E, Integrable (fun p : SectorP m=> f ((p,r.1),r.2)) (Px m)) ∧
    (∀ i, Ultra (pruning i (carpet (Px m) f)) ∧ Reflect (pruning i (carpet (Px m) f)) ∧
      ∀ p : ℝ × E, IntervalIntegrable (fun t : ℝ => Arc.d (Arc.d (pruning i (carpet (Px m) f)))
        (t*p.1,p.2)) MeasureTheory.volume 0 1) ∧
    ∀ x : E, Integrable (fun r : ℝ => (r:ℂ)^(2*s+1) * pruning (m+1) (carpet (Px m) f) (r,x)) μhalf := by
   intro f
   have hf : Sweeping f := cutSweep W h he ht (form_rephase hx A) hy
   let g := carpet (Px m) f
   have hv : Ultra g := Q.Gquiet (Px m) hf.1
   have hp : Reflect g := mirror_r (Px m) hf.2
   refine ⟨fun p=> (Q.Gmajor _ hf.1 ()).values p,
     fun i=> ⟨ (pruned hv (fun _=>hp) i).1,(pruned hv (fun _=>hp) i).2 (), fun p=> ?_⟩,
     fun x=> meets ((pruned hv (fun _=>hp) _).1) hs x⟩
   exact ((fresh (fresh ((pruned hv (fun _=>hp) _).1.smooth ()))).continuous.comp
     (show Continuous (fun t : ℝ=> (t*p.1,p.2)) by fun_prop)).intervalIntegrable 0 1

omit hs in
theorem pin_chart (s : ℂ) (A : QP) (y : ℝ) : fieldVal (pinned K s y A X Y m) W= tenorK s y • swoop s (Px m) m
   (cutWing K (rephase A X) Y W) := by
   funext x; refine congr_arg (tenorK s y * ·) (?_ : swoop s _ m (cutWing K (rephase A X) Y (ray (sail W x))) (1:ℝ)=swoop s _ m (cutWing K (rephase A X) Y W) x)
   · exact Sweep_eq (F:=SectorP m) (Px m) m s (cutSweep (ray (sail W x)) h he ht (form_rephase hx A) hy)
       (cutSweep W h he ht (form_rephase hx A) hy) 1 x (fun p=> by simp only [cutWing,ray_sail])

omit he ht hy hs in
private theorem field_swing (s : ℂ) : swoop s (Px m) m (wing s K X W) = fieldVal (ocean s K X m) W :=
   (oceanic (Z:=fun _=>s) (fun _=> const_sc _) hx.price h.price (fun _=>zero_le_one) () W).symm

theorem cut_reads : swoop s (Px m) m (cutWing K X Y W)= fieldVal (sweptRef s K X Y m) W := by
   rw [cut_projection W h he ht hx hy s]
   have hl(l r:Touch G m E) : Sweeping (Lfac s K X Y l r) := Sweep_mult _ (hy.price m E r) (sweepSelf l h hx s)
   have hr(l r:Touch G m E) : Sweeping (Rfac s K X Y l r) := Sweep_mult _ (hx.price m E l) (sweepSelf r h hy s)
   obtain hu:= sweepSelf W h (form_weave hx hy) s; obtain hv:= Sweep_gathers _ W _ (fun l r _=> hl l r);
   unfold μ_tree; rw [Sweep_reads_sub _ hs (Sweep_sub hu hv) (Sweep_gathers _ W _ (fun l r _=> hr l r)) m,
     Sweep_reads_sub _ hs hu hv,
     Sweep_reads_splits _ W _ (fun l r _=> hl l r) _ hs m,
     Sweep_reads_splits _ W _ (fun l r _=> hr l r) _ hs m];
   funext p; unfold Rfac Lfac SweepScat
   simp_rw [ Sweep_reads_factors (x:=fieldVal (Y m) _) (hy.price m E _) (Px m) (sweepSelf _ h hx _),
     Sweep_reads_factors (x:=fieldVal (X m) _) (hx.price m E _) (Px m) (sweepSelf _ h hy _),
     field_swing _ h hx, field_swing _ h hy,field_swing _ h (form_weave hx hy)]
   unfold sweptRef weave fieldVal; simp_rw [Pi.sub_apply,Pi.mul_apply,scattered,sail_scatter, mul_comm (X m _)]; -- phase orientation second

theorem placedEq (A : QP) (y : ℝ) : pinned K s y A X Y=tenorK s y • sweptRef s K (rephase A X) Y := by
   funext m w; unfold pinned; rw [cut_reads (ray w) h he ht (form_rephase hx A) hy hs]
   unfold fieldVal; rw [ray_sail]; rfl

end YM.MS.ScaleForest
