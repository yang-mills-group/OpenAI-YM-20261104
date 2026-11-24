import YM.FVA2.Lambda.Match
/-!
# Read y derivatives (and values) of matched marginal jets directly from scale flow

 Compare in the log-polynomial family at *every* y so as to infer literal exact difference
 when RHS is y-stationary in x. No derivative of an error estimate. These formulae are a
 route to a direct continuum calculation avoiding a lattice-side Re expression for beta.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Canvas
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City MS.Book.Program MS.Logarithm MS.High.Knobs
open _root_.YM.MS.Shine
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{k m n a:ℕ}
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
abbrev high (X:T (Flats G)): Recount G:= Archive 4 X
abbrev trigger (X:T ( Flats G )) (n:ℕ): Reading G:= (spaceD G).recu 1 (2:ℂ)⁻¹ (high X) (high X) n
variable (x y t:ℝ)(w:List (Lane4 G))
include hm
lemma dims (s:ℝ)(hx:fieldDim wfield w+k=4): torch k (high X n (x,t)) w = torch k (high X n (x+s,t-s)) w:= by
   have he : mass (m:=0) w + k= ((4:ℕ):ℤ):= hx; obtain ht:= Host.host (gang (hm n)); change torch k (hereZ 4 (X n) t x 0) w = _; let G':= hereZ 4 (X n) (t-s) (x+s)
   rw [← t_bud _ he, MS.Port.Can ht s,Tad_scale ( ( blade0 (s:=t-s) ( y:=x+s) ht ).price),Pi.smul_apply,Pi.smul_apply,t_bud _ he, show (-(↑(4:ℕ)):ℂ)+ (↑(4:ℕ):ℂ)=0 from neg_add_cancel _, amount,mul_zero,Complex.exp_zero,one_smul]; rfl
variable (hw: Course true w)(hp:0<w.length)(hn:1≤n)
include hw hp hn
lemma smooth (t:ℝ×ℝ): ContDiff ℝ ∞ (fieldVal (high X n t) (ray w)):= ( ( Outlook.dock hm wisdom ).master.road ℝ (ray w) n hn ( fun _=> (ray_len w).symm ▸ hp ) ( ray_course hw ) ).1 _
lemma rhythm (k:ℕ): Scale.Rhythm (fun x=> torch k ( high X n (x,t)) w):= by
   obtain ⟨N,h⟩:= ( Outlook.dock hm wisdom ).master.poly n
   have he (x:ℝ): torch k ( high X n (x,t)) w= ∑ i ∈ Finset.range N,(↑((Logarithm.plate N i).eval x):ℂ)* torch k ( high X n ( (i:ℝ),t )) w:= by
      let f(i:ℕ):=fieldVal ( high X n ( (i:ℝ),t)) ( ray w ); let c(i:ℕ):ℂ:= ((Logarithm.plate N i).eval x:ℝ); simp_rw [torch_at,← read_const]; change _=∑ i∈Finset.range N, reading k (fun t=> (c i)*f i t); rw [ ← Plane.read_sum (s:=Finset.range N) (j:=k) (f:=fun (i:ℕ) (p:ℝ)=> (c i)* f i p) (fun i _=> by exact contDiff_const.mul (smooth hm w hw hp hn _)) ] -- maybe rw
      apply congr_arg; funext p; obtain he:= congr_fun (congr_fun (interpret h x) t) (sail (ray w) p); unfold Logarithm.evaluate at he; simp only [Finset.sum_apply] at he; exact he
   rw [funext he]; apply Scale.Rhythm.sum ( Finset.range N ); intro i _; exact ( show Scale.Rhythm _ from ⟨_,Scale.Price.daylight _⟩ ).mul ( Scale.Rhythm.const _ )
-- RHS derivative of jet in t, not just continuity. useful even other Taylor orders.
lemma scaleD (s y:ℝ)(k:ℕ): HasDerivAt (fun t:ℝ=> torch k ( high X n (s,t)) w) (torch k (trigger X n (s,y)) w) y:= by
    obtain ht:= ( ( Outlook.dock hm wisdom ).master.road ℝ (ray w) n hn ( fun _=> (ray_len w).symm ▸ hp ) ( ray_course hw ) ).2.2 s y 0 k
    obtain hL := (ContinuousMultilinearMap.apply ℝ _ ℂ (fun _ : Fin k=> (1:ℝ))).hasFDerivAt.comp_hasDerivAt _ ht
    exact hL.const_smul _ -- check
lemma fee (x:ℝ)(hx:fieldDim wfield w+k=4): HasDerivAt (fun x:ℝ=> torch k ( high X n (x,t)) w) (torch k (trigger X n (x,t)) w) x:= by
    have he(a:ℝ): torch k ( high X n (a,t)) w= torch k ( high X n (x,a + (t-x))) w:= by rw [ dims hm a t w ( x-a ) hx, add_sub_cancel, show t-(x-a)=a+(t-x) from (by abel) ]
    simp_rw [he]; have h: HasDerivAt (fun t:ℝ=> torch k ( high X n (x,t)) w) (torch k (trigger X n (x,t)) w) (x+(t-x)):= by rw [add_sub_cancel]; exact (scaleD hm w hw hp hn x t k)
    obtain hV:= HasDerivAt.scomp x h ( (hasDerivAt_id' x).add_const (t-x)); rw [one_smul] at hV; exact hV
lemma shifted(y:ℝ)(hx:fieldDim wfield w+k=4): Scale.Rhythm (fun t=> torch k ( high X n (y,t)) w):= by
        have HT(t:ℝ): torch k ( high X n (y,t)) w= torch k ( high X n (y+t,0)) w:=by rw [dims hm _ t w t hx, sub_self]
        rw [ funext HT ]; obtain hv:= (rhythm hm 0 w hw hp hn k).pre (Polynomial.C y + Polynomial.X); simp_rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at hv; exact hv
variable (h:G.Simple){p:Team}(ht:Fixed ( col ( skyline G p ) ) ( high X ) true 4 1)
include ht h
lemma exact_scale (x:ℝ)(hx:fieldDim wfield w+k=4)(f:ℂ)(Hf:∀ y:ℝ, torch k ( skyline G p n x (exp y)) w- torch k ( skyline G p n 0 (exp y)) w=f): torch k ( high X n (x,t)) w- torch k ( high X n (0,t)) w=f:= by
    let F t:=( torch k ( high X n (x,t)) w- torch k ( high X n (0,t)) w )-f
    have hF:Scale.Rhythm F:= ((shifted hm w hw hp hn x hx).sub (shifted hm w hw hp hn 0 hx)).sub (Scale.Rhythm.const _); apply sub_eq_zero.mp; apply congr_fun ( Scale.Rhythm.asleep hF _ ) t
    let U:=col (skyline G p); have hV y :Tendsto (fun t:ℝ=> torch k ( U n (y,t)) w- torch k (high X n (y,t)) w) atTop (𝓝 0):= by
        have hs (t:ℝ):ContDiff ℝ ∞ (fieldVal (U n (y,t)) (ray w)):= ( SatSolve h (skyPC G p) |>.road ℝ (ray w) n hn ( fun _=> (ray_len w).symm ▸ hp ) ( ray_course hw ) ).1 _
        obtain hv:= Hue.Agent.Signal.fade_v y w (ht n hn _ (fun _=> hp)) hw rfl hx.le (fun t=> ( hs t ).sub ( smooth hm _ hw hp hn _ )); apply hv.congr; intro i; rw [Pi.sub_apply,torch_sub w (hs _) (smooth hm w hw hp hn _)]
    obtain H:= (hV 0).sub (hV x); rw [ sub_self ] at H; apply H.congr; intro i; unfold F U col; rw [← Hf i]; abel
omit hp hn -- force apply later
open Hue.Agent
-- projections equal effective *counterterms*, no numerical consequences until shell integrals evaluated
lemma waveK (hl:w.length=2)(hx:fieldDim wfield w+k=4): let A (x:ℝ):= ranktwo (2*((-(p 2).waveA).eval x)) ((-(p 2).waveC).eval x-(-(p 2).waveA).eval x) w;
       torch k ( high X 2 (x,t)) w- torch k ( high X 2 (0,t)) w=A x-A 0:= by intro A; have hp := Kappa.sits (Hue.Agent.Signal.all h hm ht ); apply exact_scale hm t w hw (by omega) (by decide) h ht x hx; intro i; obtain ha:= Finite.second hp x (exp i) w hw hl hx.le; obtain h':= Finite.second hp 0 (exp i) w hw hl hx.le; rw [if_pos hx] at h' ha; rw [ show A x = _ from ha.symm, show A (0:ℝ)=_ from h'.symm ]; abel
omit hw in
lemma pivot (i j k:G.ColorIndex): Mark.token (high X 3 (x,t)) i j k-Mark.token (high X 3 (0,t)) i j k= ((( p 3 ).coupling.eval x+(p 2).waveC.eval x)-( (p 3).coupling.eval 0+(p 2).waveC.eval 0 ):ℝ ) * (Mark.LieColor i j k:ℂ) := by
    let χ:= [Detect.S i 0,C j 0,C k 0]; have he(F:Law G): Mark.token F i j k=torch 0 F χ:= by simp [Mark.token, torch_at,χ,reading]
    rw [ he, he ]; apply exact_scale hm t χ (fun _=>by simp [χ, C,Detect.S,qnote,net] ) (by simp [χ]) (by decide) h ht x rfl; intro y; rw [ ← he, ← he ]; exact Finite.third (Kappa.sits ( Hue.Agent.Signal.all h hm ht )) ..
end YM.FVA2.Lambda.Canvas
