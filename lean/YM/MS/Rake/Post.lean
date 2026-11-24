import YM.MS.Rake.Live
/-!
# Lattice & continuum rows meet preferences for low and comfort.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Logarithm LogTime
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type}[ NormedAddCommGroup E ][NormedSpace ℝ E] {T y:ℝ}{q:ℤ}{b c b':Bool}{d:ℕ}
 {S:Scale I}{X:Wind.Dec G}{K: Belt I}{U W:Recount G}{a η:I→ℝ}
lemma periodT (u: Wind.Flow G)(H: Bon b q u)(i:ℕ)(v:Fin i→ BH G)(n:ℕ)(t:ℝ) : Villa (fun t p=> u t (Local.gaze v p)) t n Set.univ:= by
    letI: ProperSpace (Fin i→QP):= FiniteDimensional.proper ℝ _; refine Villa.moves ( C:=4*π ) ?_ ?_ t n
    · convert! jointWay H.joint ( Local.arr v ) using 1; ext; simp [uncurry,Local.at_arr]
    intro t p; obtain ⟨ z,Q,hz,rfl⟩:= Wind.realm p; refine ⟨ z,hz,1,norm_one .., funext fun s=>?_ ⟩; rw [ show z+amt Q-z=amt Q from add_sub_cancel_left .., one_smul]; exact altSpace ( H.perk t) i v s Q []
lemma costume (u: Wind.Flow G)(H: Bon b q u)(hx:∀ i,‖a i‖≤T)(hp:∀ i, S.length i=1) : Lease b' c S (fun i=> u (a i) ) 1:= by -- b' binder
    intro E _ _ w hv hc; let L: E→L[ℝ] ( Fin w.length→ QP ):= ContinuousLinearMap.pi fun i=>(w.get i).2; let y(i:Fin w.length):=(w.get i).1; let F t p := u t (Local.gaze y p); have ht : ContDiff ℝ ∞ (Function.uncurry F):= by convert! jointWay H.joint ( Local.arr y ) using 1; ext; simp [F,uncurry,Local.at_arr];
    have hZ (p:E): sail w p= Local.gaze y ( L p ):= by apply List.ext_getElem; all_goals simp [sail,L,Local.gaze,y]
    unfold Cape Plane.Chart; simp_rw [hZ,hp]; simp; exact Bound.linear L ( season ht (fun i=>(hp i).ge) hx (fun j=>periodT u H _ y j T) ) -- p.unit defeq
lemma daylight (p:Polynomial ℝ) (t:I→ℝ) (h:paid S (fun i=>‖ t i‖) 1):Bound S (fun i (_:E)=> p.eval (t i)) 1:= by
    -- powered with basic via pow
    induction p using Polynomial.induction_on' with
    | add p q hp hv=> simp only [ Polynomial.eval_add ]; exact Costs.add hp hv
    | monomial n a=>
        have he:Bound S (fun i (_:E)=>t i) 1:= Costs.scalar (paid_at h ( fun _=>zero_le_one)); simp only [Polynomial.eval_monomial]; convert! ( ( Costs.L (ContinuousLinearMap.mul ℝ ℝ a) ( he.pow n )) ) using 1; ext i; simp
lemma maximumT (hx:∀ i,‖a i‖≤T)(hS:∀ i,S.length i=1) (P: Wind.Pack G)(hp:Fees b q P) (he: paid S (fun i=>‖η i‖) 1): Lease b' c S (fun i=> P (η i) (a i)) 1:= by -- b' add
    obtain ⟨N,hN⟩:= hp.currency; rw [ show (fun i=>P (η i) (a i))=(fun i=>∑ j∈ Finset.range N,( Logarithm.plate N j).eval (η i) • P (j:ℝ) (a i) ) from funext fun i=> (by nth_rw 1 [interpret hN (η i)]; simp [Logarithm.evaluate] ) ]; refine Lease.sum _ (fun i _=>?_) (fun _=>zero_le_one);
    intro E _ _ w hu hb; let f:= costume (P (i:ℝ)) (hp.stay _) hx hS (c:=c) E w hu hb; convert ( ( daylight ( E:=E ) ( Logarithm.plate N i ) _ he ).smul f ) using 1; rfl; ext; simp -- maybe cast issues
abbrev dawn (K:Belt I):= K.price
-- Heta time prescription.swept ℝ-recount.
def nameR (F:Reading G)(η:I→ℝ): Glade G I:= fun i t=>F (η i,t)
lemma nameWarm (p:Pack G)(h:Fees b q p): Warm (fun i t=> p (η i) ( exp t )) b':= by
   constructor; · intro i T hT; let t:= exp T; exact maximumT (c:=false) (η:=fun _=>η i) (S:=Job.single (camp T)) (a:=fun u:camp T=> exp (tstart u)) (T:=t) (fun p=>( ( Real.norm_of_nonneg (exp_pos _).le ).le.trans (raise_here p))) (fun _=> rfl) p h ⟨‖η i‖+1,(by positivity),0,fun _=>by simp⟩
   intro i w hw; exact (h.stay (η i) |>.joint.at_const _ w Real.contDiff_exp).continuous
lemma nameD {F:Pearl.Flats G}(h:Emit.Host F d)(hp:∀ i,exp ( a i )= S.length i)(hv:∀ i, ‖η i + a i‖ ≤ S.basic i ) : Lease b c S (fun i=> Outlook.four d F (η i,a i)) ( fun i=> S.length i ^ ( -(d:ℤ) ) ) := by -- names
   intro E _ _ w _ _; convert! Outlook.bills ( m:=0 ) S h w hv hp using 1; funext i; rw [ ← zpow_add₀ (S.pos i).ne' ]; rfl
end YM.MS.Rake
