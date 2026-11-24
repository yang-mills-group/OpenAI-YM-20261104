import YM.FVA2.Lambda.Extract
/-! # The three actual tests in the slope computation

`pole` here = first derivative in the scale parameter. See `AtLast` for the
calculation on the specified MS scheme combining the results. -/
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
-- Read slope of the group from the actual three tests at zero scale (point x,t arbitrary).
open Complex (I)
variable (x t:ℝ)
open MS.Landau.Detect.Mark
variable (h:G.Simple){p:Team}(ht:Fixed ( col ( skyline G p ) ) ( high X ) true 4 1)
lemma trackP (p:Polynomial ℝ) (x:ℝ): HasDerivAt (fun x:ℝ=> ( ( p.eval x:ℝ ):ℂ )) (↑((Polynomial.derivative p).eval x):ℂ) x:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (p.hasDerivAt x)
include h ht hm
def pole (p:Polynomial ℝ)(x:ℝ):ℝ:= (Polynomial.derivative p).eval x
abbrev letters (i:G.ColorIndex) := [ Detect.W 1 i (spray 0), Detect.W 1 i (-spray 0) ]
abbrev ghosts (i:G.ColorIndex) := [ Detect.C i (spray 0), Detect.U 0 i (-(spray 0)) ]
lemma salaries (i:G.ColorIndex): torch 2 (trigger X 2 (x,t)) (letters i)= -(2:ℂ) * ( pole (p 2).waveA x:ℂ ) := by
   let w:= letters i; have hx: Course true w:= fun _=> by simp [w,letters,W,qnote,net]
   obtain H:= ( fee (k:=2) hm t w hx (by simp [w,letters]) (by decide : 1≤2) x rfl ).sub_const (torch 2 ( high X 2 (0,t) ) w);
   have he(y:ℝ): torch 2 ( high X 2 (y,t) ) w- torch 2 ( high X 2 (0,t) ) w= (-2:ℂ)*(↑((p 2).waveA.eval y):ℂ) - (-2:ℂ)*(↑((p 2).waveA.eval 0):ℂ) := by
     rw [waveK hm y t w hx h ht rfl rfl]; simp [ ranktwo,w,kinds,spray,delta, Momentum.sq,Landau.precision,Pi.single_apply,ite_pow ]
   simp_rw [ he ] at H; exact H.unique (((trackP (p 2).waveA x).const_mul (-2:ℂ)).sub_const _)
lemma chargeC (i:G.ColorIndex): torch 1 (trigger X 2 (x,t)) (ghosts i) = (( pole (p 2).waveA x:ℂ ) - ( pole (p 2).waveC x:ℂ )) * I:= by
   let w:=ghosts i; have hx: Course true w:= fun _=> by simp [w,ghosts,C,U,qnote,net]
   obtain H:= ( fee (k:=1) hm t w hx (by simp [w,ghosts]) (by decide :1≤2) x rfl ).sub_const (torch 1 ( high X 2 (0,t)) w)
   have he (y:ℝ): torch 1 ( high X 2 (y,t)) w-torch 1 ( high X 2 (0,t)) w=(↑((p 2).waveA.eval y) - (↑((p 2).waveC.eval y):ℂ))*I-(↑((p 2).waveA.eval 0)-( ↑((p 2).waveC.eval 0):ℂ))*I:= by rw [waveK hm y t w hx h ht rfl rfl]; simp [ranktwo,kinds,w,spray]; ring
   simp_rw [he] at H; exact H.unique ((( ( trackP (p 2).waveA x).fun_sub ( trackP (p 2).waveC x)).mul_const I).sub_const _)
lemma ghost_tok(i j k:G.ColorIndex): token ( trigger X 3 (x,t) ) i j k=( ( pole (p 3).coupling x:ℂ ) + (pole (p 2).waveC x:ℂ) ) * (LieColor i j k:ℂ):= by
   let w:= [Detect.S i 0,C j 0,C k 0]; have hx: Course true w:= fun _=> by simp [w,Detect.S,C,qnote,net]
   have ht'(F:Law G): token F i j k=torch 0 F w:= by simp [Mark.token,w,torch_at,reading];
   obtain H:= (fee (k:=0) hm t w hx (by simp [w]) (by decide : 1≤3) x rfl).sub_const ( torch 0 (high X 3 (0,t)) w ); simp_rw [← ht', pivot hm _ t h ht i j k] at H; push_cast at H;
   apply H.unique -- calc
   convert! ( ( ( trackP (p 3).coupling x ).fun_add ( trackP (p 2).waveC x )|>.sub_const _ ).mul_const ( LieColor i j k:ℂ ) ) -- check
end YM.FVA2.Lambda.Canvas
