import YM.MS.High.Logs
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Labels
/-!
# High recipes tested on both flows

`t` in this formalization is log heat length (manuscript $R$, RG t denotes
another variable depending section), and `y` logarithm of native MS scale (`μ`).
Choice coefficients may depend polynomially on y. Intertwining equality used on
conserved kernels only. These statements of the master equation,
unphysical-field version, supplied from both regulator constructions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm
open scoped Topology ContDiff
variable {G : Gauge} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ℝ}

def meet : IntervalFamily ℝ := {
   beg _:=0
   window _:= Set.Ici 0
   beg_nn _:=le_rfl
   ci _:=Subset.rfl -- namespace?
   used _:=by simp
   ord _:=ordConnected_Ici
   logPart x:=1+|x|
   lg _:=by simp }
-- price a and cap 
lemma meet_start (i : ℝ) : meet.window i=Set.Ici (meet.beg i):= rfl
abbrev eps_gain : ℝ:=1/2
lemma p_gain : 0<eps_gain:= by norm_num [eps_gain]
lemma s_gain : eps_gain<1:= by norm_num [eps_gain]
abbrev fig (b : Bool) (r:ℕ): Prop:= b=true → 0<r
abbrev Reading (G:Gauge):= Clock ℝ → Law G
abbrev Recount (G:Gauge):= ℕ→ Reading G
abbrev Needle (G : Gauge):= Domain (Landau.parity (A:= Axis) (C:=CI G)) FourP
abbrev spaceL (G:Gauge): Needle G := zL Axis G.ColorIndex
abbrev spaceD (G:Gauge): Needle G := zD Axis G.ColorIndex

-- y polynomial with a common degree, versions sweeping all positions at once.
def stamp (F : Reading G) : Prop:= Ready (fun v:ℝ=>fun t:ℝ=> F (v,t))
-- Actual dimension steps for constructing estimates
abbrev Bill (F : Reading G) (w : Wire (Branch G Axis) E FourP) (h:ℤ): Prop:= herecost meet F w h wfield
abbrev Trust (b : Bool) (h : ℤ) (F F' : Reading G) (r : ℕ) := Match meet.primary b (lane meet F) (lane meet F') h (rate meet eps_gain) wfield r

-- Single master structure differs only by chosen charge & meshed laplacian.
def degreeMaster (p : FourP→FourP) (X: Needle G): Needle G:={X with meter t:= choir ( Landau.laplace (Landau.low (exp t))) p}
def Ward (p : FourP→FourP) (X: Needle G) (n d:ℕ) (C:ℂ) (g f : Recount G) (x:Clock ℝ) : Law G:= -((degreeMaster p X).recu d C g f n x)
structure Spheres (p:FourP→FourP) (X : Needle G) (B : Recount G) (F:Recount G) (ch:ℂ) (d:ℕ) (b:Bool): Prop where
    road : Flow X b d ch B F
    rank n : ∃ r, ∀ t, Upper b r (F n t)
    trueC n t : Solid b (F n t) 0
    reflects n t: b=true → SignedScope b (F n t) -- bulk
    poly n: stamp (F n)
    qfm n t w: d≤n → fig b w.length → Course b w → (send p).raise (F n t) w=Ward p X n d ch B F t w
-- nonvity standard/gating dependent

def Good (b:Bool) (G:Gauge) (h:ℤ) (F:Recount G) := ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ n (w:Wire (Branch G Axis) E FourP), Course b w→fig b w.length→ Bill (F n) w h
-- h may vary; on dawn exp(...) factor=1 at meet. Explicit.
def Rising (b:Bool) (F:Recount G):= ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ n (w:Wire (Branch G Axis) E FourP), Course b w→ fig b w.length→ Bound meet.dawn (fun i x=> F n (i,0) (sail w x)) fun _=>1
variable {w : Wire (Branch G Axis) E FourP} {F K: Reading G} {B B' f f' : Recount G} {r d n:ℕ} {b:Bool} {ch:ℂ} {h:ℤ}
lemma zero_ext (hv:∀ t u, Course b u→ u.length=r→ F t u=0) (hw:∀ t u, Course b u→ u.length=r→ K t u=0) : Trust b h F K r := by
   refine Plane.match_agrees meet.primary b (r:=r) (f:=0) (g:=0) ?_ ?_ ?_
   · exact fun i w hh hu=> (hv _ w hh hu).symm
   · exact fun i w hh hu=> (hw _ w hh hu).symm
   exact fun E _ _ w _ _=> Like.zero (fun i q _=> zpow_nonneg (meet.primary.pos _).le _) (fun i=> (Plane.at_start p_gain.le i).1.le)

section costs
variable (hw: Course b w) (HO : Trust b h (f n) (f' n) (w.length+2))
   (he : ∀ i ∈ paths n d,∀ r,Trust true 4 (B (n-i)) (B' (n-i)) (r+1))
   (hq : ∀ i∈ paths n d, ∀ r,Trust b h (f i) (f' i) (r+1))
include hw HO he hq
lemma first_rhs : Light meet.primary (rate meet eps_gain) wfield (lane meet ((spaceL G).recu d ch B f n)) (lane meet ((spaceD G).recu d ch B' f' n)) w h := land_value s_gain.le (by simp) n d ch hw HO he hq
lemma second_rhs : Light meet.primary (rate meet eps_gain) wfield (lane meet (Ward wave (spaceL G) n d ch B f)) (lane meet (Ward id (spaceD G) n d ch B' f')) w (h+1):= by
   let X:= degreeMaster wave (spaceL G); let Y:= degreeMaster id (spaceD G); haveI : MeasureTheory.Measure.IsAddHaarMeasure Y.measure:= measure_spec
   have hW : Light meet.primary (rate meet eps_gain) wfield (lane meet (X.recu d ch B f n)) (lane meet (Y.recu d ch B' f' n)) w (h+1):= by
       let Q := lap_meter (C:=G.ColorIndex) (A:= Axis) (fun i:meet.Inst=> Real.one_le_exp ((meet.beg_nn _).trans i.ge)) (primary_large s_gain.le)
       convert! recu_cost meet X Y (firstZone Axis) rfl measurableSet_closedBall zone' 2 (primary_large s_gain.le) (by simp [FourP]) Q n d ch hw HO he hq using 1; omega
   exact Like.neg hW
end costs
end YM.MS.High
