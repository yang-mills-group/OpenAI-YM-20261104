import YM.FVA2.Scale.Reach
/-!
# Separated continuum arrays and action on them

`Equator.wave` is on the MS theory. See `Pace` about the polynomial-in-log-scale
criterion, and `clocks`/`smooth` here for showing the response to a scale change
with the indicated `MS_Data` (in the comparison setting,
not assuming the polynomial-in-log-scale response).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point
variable {G:Gauge} {n d k e:ℕ}
abbrev Stage (n:ℕ):= { x : Points n // x∈ conf n }
abbrev Way (G:Gauge)(d:ℕ) := (n:ℕ)→ Stage n → T (Structure1.Point G d n)
abbrev Inherited (A:Way G d)(B:Way G e)(h:d≤e): Prop:= ∀ n (p:Stage n) k (v:Tags G d n), A n p k v=B n p k ( up h ∘ v )
variable (A: Way G d)
namespace Facets
def actMark (S:Guard G d)(A:Way G d): Way G d:= fun n x=> status S (A n x)
def posing (t:ℝ)(x: Stage n): Stage n:= ⟨ Real.exp (-t) • x.val,Extent.placed t x.val x.property ⟩
def scaling (t:ℝ)(A:Way G d): Way G d:= fun n x i=> ( A n (posing t x) i ).compLinearMap (fun _=> Level.Dial d t)
def couple (q:Cn)(A:Way G d): Way G d:= fun n x=> Program.substitute q ( A n x )
-- compose on right, including true ±t scaling group & geometric Jac.Engineering.V.
local notation "Γ"=> (Guard G d)
variable (S W:Guard G d)(t v:ℝ)(q r:Cn)
lemma scale_at (x: Stage n)(p:Tags G d n): scaling t A n x k p=A n (posing t x) k (Level.Dial d t ∘ p):=rfl
lemma at_pose (x:Stage n): posing v (posing t x)=posing (v+t) x:=Subtype.ext (by change Real.exp (-v) • (Real.exp (-t) • x.val)=_; rw [←mul_smul, ← Real.exp_add, ← neg_add ]; rfl)
lemma scales : scaling t (scaling v A)= scaling (v+t) A:= by
    ext1 n; ext1 x; ext1 i; ext1 p; simp only [scale_at, at_pose ]; apply congr_arg; funext j; exact ( DFunLike.congr_fun ( Level.group (G:=G) (d:=d) v t ) (p j) )
lemma stand_s : scaling 0 A=A:= by
    ext1 n; ext1 x; ext1 i; ext1 p; rw [scale_at,Level.flat,show posing 0 x=x from Subtype.ext ( by change Real.exp (-(0:ℝ)) • x.val=_; simp)]; rfl
lemma acts : actMark S (actMark W A)=actMark (W*S) A:= funext fun _=> funext (fun _=> Reg.Point.eternal W S _ )
lemma acts_h : actMark 1 A=A:= funext (fun _=> funext (fun _=>Reg.Point.home_v _))
lemma pose_act : scaling t (actMark S A)= actMark (convertT t S) (scaling t A):= by
    ext1 n; ext1 x; ext1 i; ext1 p; rw [scale_at]; unfold actMark; simp_rw [seen,scale_at]; refine Finset.sum_congr rfl (fun j _=>?_); apply congr_arg; funext i; have H: coeff (j (some i)) (convertT t S)=turner t (coeff (j (some i)) S):= coeff_mk ..; unfold pulseU Function.comp; dsimp only; rw [ H ]; exact (DFunLike.congr_fun (Level.transfer (G:=G) t (PowerSeries.coeff (j (some i)) S)) (p i))
lemma couple_s : scaling t (couple q A)= couple q (scaling t A):= by
    ext1 n; ext1 x; ext1 i; ext1 p; rw [scale_at]; unfold couple; simp_rw [Dframe.translate,rules,scale_at]
lemma team (h:Rooted q): actMark (stepV q S) (couple q A)=couple q (actMark S A):= funext fun _=> funext fun _=> resetP q S _ h
lemma double (h:Rooted q)(hv:Rooted r): couple r (couple q A)=couple (q.subst r) A:= funext fun _=> funext fun _=> Reg.Point.cycles _ q r h hv
lemma team_one : couple X A=A:= by
    ext1 n; ext1 x; have H:Rooted (X:Cn):= by simp [Rooted]
    ext1 i; ext1 p; unfold couple; obtain h:= ( moves (A n x) p H ).trans (X_subst _); replace h:=congr_arg (coeff i) h; simp_rw [ Reg.Point.story, coeff_mk ] at h; exact h -- subst_X? X_subst orientation
lemma unfold_acts (h:d≤e)(W:Guard G e)(B:Way G e)(H:Inherited A B h)(V:Walk h S W): Inherited (actMark S A) (actMark W B) h:= by
    intro n p k v; unfold actMark; simp_rw [seen]; apply Finset.sum_congr rfl; intro i _; rw [ H ]; apply congr_arg; funext l; exact (V _ _ ).symm
lemma unfold_scale (h:d≤e)(B:Way G e)(H:Inherited A B h): Inherited (scaling t A) (scaling t B) h:= by
    intro n p k x; rw [scale_at,H,scale_at]; apply congr_arg; funext i; exact ( Level.chain _ _ _ ).symm
lemma unfold_team (h:d≤e)(B:Way G e)(H:Inherited A B h): Inherited (couple q A) (couple q B) h:= by intro n p k v; unfold couple; simp_rw [ Dframe.translate,H ]
end Facets
open Reg.Point Facets
namespace Equator
variable (ν:ℝ) {O:Booked (Press.portDeck G)}(T: MS_Data G O)
def wave (d:ℕ): Way G d:= fun _ x=> meteor ν T d x.val
local notation "B"=> (Press.portDeck G)
variable (Y: Initialize G) (S:Prescription (Press.portDeck G))
abbrev iris (x:Stage n): XSpace.Structure1.Point G d n:= scene x.val d
def StarGround (A:Way G d): Prop:= ∀ n (p:Stage n), A n p 0=iris p
def PurePower (A:Way G d): Prop:= ∀ n (p:Stage n) (v: Tags G d n)(i:ℕ), Rhythm (fun s=> scaling s A n p i v)
lemma before : StarGround (wave ν T d):= fun _ p=> limit_lead ν T p.property
lemma step_dawn (P:Cn)(h:StarGround A): StarGround (couple P A):= fun n p=> ( pay0 .. ).trans (h n p)
lemma step_mark (P:Guard G d)(h:Base P)(hp:StarGround A): StarGround (actMark P A):= fun n p=> MultilinearMap.ext (fun _=> (Silver.status_lead ..).trans (by rw [hp,h.zero]; rfl ) ) -- maybe overloading
lemma wave_walk (h:d≤e): Inherited (wave ν T d) (wave ν T e) h:= by intro n p k x; exact ( Reg.State.initial_chain ν T h p.val x ).symm
lemma powers_t (P:Cn)(h: PurePower A): PurePower ( couple P A ):= by intro n p v i; simp_rw [Facets.couple_s, couple,Dframe.translate,rules,smul_eq_mul]; exact Rhythm.sum _ (fun x _=> Rhythm.mul ( Rhythm.const _ ) ( h _ p v x )) -- stuck type of G.
lemma powers_m (P:Guard G d)(h:PurePower A)(hu:Native P): PurePower (actMark P A):= by intro n p v i; simp_rw [ pose_act, old_g _ _ hu, actMark, seen ]; exact Rhythm.sum _ fun x _=> h ..
lemma powers_s (s:ℝ)(h:PurePower A) : PurePower (scaling s A):= by
    intro n p v i; simp_rw [scales]; have hu(x:ℝ): Polynomial.eval x ((Polynomial.C s)+Polynomial.X)=s+x:= ( by rw [Polynomial.eval_add (R:=ℝ), Polynomial.eval_C (R:=ℝ), Polynomial.eval_X (R:=ℝ)] ); have H:= (h _ p v i).pre ( (Polynomial.C s)+Polynomial.X ); simp_rw [hu] at H; exact H
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
include h hs
theorem clocks (t:ℝ): scaling t (wave ν T d)=wave (ν-t) T d:= by
    ext1 n; ext1 x; ext1 i; ext1 p; rw [ stencil_he _ p, stencil_he (wave _ _ _ _ _ _) p ]; apply Finset.sum_congr rfl; intro j _; congr 1; rw [scale_at,show Level.Dial d t ∘ fill j=(fun a=> Extent.token t (j a).size • fill j a) from funext (fun i=> Level.exact₀ _ _) ]; exact Extent.declares t x.val ν Y S T h hs j x.property
lemma smooth : PurePower (wave ν T d):= by
    intro n x p i; simp_rw [clocks ν T Y S h hs]; have hu(x:ℝ): Polynomial.eval x (Polynomial.C ν - Polynomial.X)=ν-x:= (by rw [Polynomial.eval_sub (R:=ℝ), Polynomial.eval_C (R:=ℝ), Polynomial.eval_X (R:=ℝ)] ); have H:= ( Known.rhythm Y S T h hs x.val x.property p i ).pre ( Polynomial.C ν- Polynomial.X ); simp_rw [hu] at H; exact H
lemma iris_s (x:Stage n)(v:Tags G d n)(t:ℝ): iris (posing t x) (Level.Dial d t ∘ v)=iris x v:= by
    rw [ ← before 0 T n ( posing t x ), ← before (0-t) T n x, ← scale_at, clocks 0 T Y S h hs ] -- scale_at parameters order?
end Equator
end YM.FVA2.Scale
