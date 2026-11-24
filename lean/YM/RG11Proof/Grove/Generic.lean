import YM.RG11Proof.Grove.Rooms
import YM.RG11Proof.Window.Outcome

/-!
# Kernel-functional shape protocols for OPE

Arbitrary correlations obtained by fixed horizon downrestriction. Compute
answers from continuum `clean` smooth-kernel functionals (using a fixed
linear extension to evaluated Test arrays): need those smooth kernel
premises on INDEPENDENT schemes or explicitly prove estimator binding to `tray`.
At any other size clipped to a bigger horizon, EXACT as distributions frompacks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Grove
open scoped Classical BigOperators
open PowerSeries YM.RG11.Jets YM.RG11.Scale YM.RG11.Nodes YM.RG11.Fields
open Maxwell Labels Function Set
variable {G:Gauge}{F:Frames G}{d n i e m:ℕ}

abbrev lab (F:Frames G)(d:ℕ):=(tower F d).toBasis.J
abbrev sheaf (F:Frames G) (n d:ℕ):= Fin n → lab F d
abbrev leverage (n:ℕ):=RG11.Stress.clean n→ₗ[ℂ] ℂ
local notation "ps"=>PowerSeries ℂ

-- f(any t-question on separated smooth kernel), announced horizon and ordered fields.
def tray (A:ShapeReport G F)(d:ℕ)(q:leverage (n+m)){hi:i≤d}{he:e≤d}(y:sheaf F n i)(z:sheaf F m e):ps:=
   RG11.Stress.survey A (tower F d).toBasis q (Fin.append (rise F hi ∘ y) (rise F he ∘ z))

-- simplest protocol exposing comparisons, canonically announces MAX horizon

def link (A:ShapeReport G F)(i e:ℕ)(q:leverage (n+m)): Rect (sheaf F n i) (sheaf F m e) ps:=
   Matrix.of fun y z=> tray A (max i e) q (hi:=(le_max_left ..)) (he:=(le_max_right ..)) y z

 theorem rise_visible (A:ShapeReport G F){d d'}(h:d≤d')(q:leverage n)(y:sheaf F n d):
    RG11.Stress.survey A (tower F d).toBasis q y=RG11.Stress.survey A (tower F d').toBasis q (rise F h ∘ y):=by
   unfold RG11.Stress.survey perceive; congr! 1; ext1 i; congr 1
   apply LinearMap.ext; intro f; change A.table i d n f _=A.table i d' n f _
   rw [show ((tower F d').b ∘ ((rise F h) ∘ y))= up F h ∘ (tower F d).b ∘ y from funext fun i=>basis_rise F h _]; exact A.packs d d' n i h f _

private theorem app_map {α β:Type*}(f:α→ β)(y:Fin n→α)(z:Fin m→α): f ∘Fin.append y z=Fin.append (f ∘ y) (f ∘ z):=by
  funext x; refine Fin.addCases (fun i=>?_) (fun i=>?_) x <;> simp

 theorem link_tray (A:ShapeReport G F)(d)(q:leverage (n+m)){hi:i≤d}{he:e≤d}(y:sheaf F n i)(z:sheaf F m e):
   link A i e q y z=tray A d q (hi:=hi) (he:=he) y z:=by
   unfold link tray
   rw [Matrix.of_apply,rise_visible _ (sup_le hi he),app_map]
   have h (a b c:ℕ)(k:a≤b)(l:b≤c){j}(u:sheaf F j a):rise F l ∘rise F k ∘u=rise F (k.trans l)∘u:=by
      funext i; exact congrArg (fun (h:(tower F a).toBasis.J ↪ (tower F c).toBasis.J)=>h (u i)) (rises_stack F k l)
   rw [h,h]

def plank {d}(V:Square (lab F d) (PowerSeries ℝ)):Square (lab F d) ps:= V.map Jets.deposit
@[simp] theorem plank_pays {d}(V:Square (lab F d) (PowerSeries ℝ))(i j):plank V i j=Jets.deposit (V i j):=rfl

def castNet {d}(V:Square (lab F d) (PowerSeries ℝ))(n:ℕ):Square (sheaf F n d) ps:=cluster (plank V) n

abbrev worth {d n:ℕ} (v:sheaf F n d):ℕ:= cluster_weight (Window.grade F d) v

 theorem plank_grade (V:Square (lab F d) (PowerSeries ℝ))(he:graded (Window.grade F d) V):graded (Window.grade F d) (plank V):=fun h=>by rw [plank_pays, he h,map_zero]

-- orientation from Window.Direction. Only A,B real parts but full holds.
namespace Matrices
variable {d n:ℕ}(A B:ShapeReport G F){X: Window.AxisData A}{S:Window.AxisData B}
variable {p:PowerSeries ℝ}{Z:∀ i,Window.SquareAt F i}(h:Window.Direction A X B S p Z)

include h in
theorem linked {m}(i j:ℕ)(q:leverage (n+m))(N):
    MatThrough N (link B i j q) (rug (Jets.deposit p) (castNet (Z i) n) (link A i j q) (Matrix.transpose (castNet (Z j) m))):=by
   let r:=max i j; let u:= (tower F r).toBasis
   let V:= Z r; let D:Change ℝ u.J:=⟨p,V⟩
   have hg:Anchored D.g:=(h.legal r).ruler.base
   have hp:= RG11.Stress.survey_match A u B hg (n:=n+m) (N:=N) (by rw [h.match_all r]; exact fun _=>Through.refl _)
   intro y z
   let e:=rise F (le_max_left i j); let l:=rise F (le_max_right i j)
   specialize hp (Fin.append (e ∘ y) (l ∘ z)) q
   unfold link tray
   rw [Matrix.of_apply]
   refine hp.symm.trans ?_
   have Hq{t}(hh:t≤r): Horizon.Held (rise F hh) ((toComplex D).Z):=fun k l hv=> by rw [show (toComplex D).Z ((rise F hh) k) l = Jets.deposit (V ((rise F hh) k) l) from rfl, show V ((rise F hh) k) l=0 from Window.holds hh (h.legal r).field k l hv, map_zero]
   change Through N (plant (plank V) (PowerSeries.subst (Jets.deposit p) ∘ RG11.Stress.survey A u q) (Fin.append (e ∘ y) (l ∘ z))) _
   rw [gathered _ (RG11.Stress.survey A u q) (plank V) e l (Hq _) (Hq _)]
   have he{t}(hh:t≤r): Horizon.take (rise F hh) (plank V)=plank (Z t):= by rw [← h.travels hh]; rfl
   rw [he,he]; exact Through.refl _
   -- rewrite using gathered
end Matrices
end YM.RG11.Grove
