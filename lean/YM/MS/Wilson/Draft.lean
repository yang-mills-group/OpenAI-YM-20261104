import YM.MS.Wilson.Energy
import YM.MS.Wilson.Sew
/-!
# Wilson cylinder analytic germs

Local embedding ports, no radius on positions needed since these start actual rank tensors.
   including left and right even when alias at wraps. `vol` polynomial (generator
 of q gauge from actual local field, unit measured at true links). Sign σ unaffected in wrapping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Draft
open Function Filter Finset Set Plane Koszul Cylinder Taylor Lab Sew Chart Lattice Bare Focus
open Landau
open scoped Topology ContDiff
variable {G : Gauge}{P Q:Type}
abbrev DotFlip {P:Type} := field (Landau.parity (A:=Axis) (C:=G.ColorIndex)) (P:=P)

-- first analytic unary on link (base color algebra only)
def onedge (x:Edge P)(F:G.Color→ℝ): Dot G P:= art (fun _:Unit=>x) (fun b:Lot G Unit=>F (b ()))
lemma onmove (r:P→Q)(x:Edge P)(F:G.Color→ℝ): transport r (onedge x F) = onedge (r x.1,x.2) F:= map_sec ..
def GH (i:Conn G)(x:P): Dot G P:= Cylinder.single (ghostAt i x)
def AHplus (i:Conn G)(x:Edge P): Dot G P := single ((anti x.2,i),x.1)
def GHplus (i:Conn G)(x:P): Dot G P:= single ((gaugeC,i),x)
lemma move_GH (r:P→Q)(i:Conn G)(x:P): transport r (GH i x)=GH i (r x):= escort ..
lemma move_AH (r:P→Q)(i:Conn G)(x:Edge P): transport r (AHplus i x)=AHplus i (r x.1,x.2):= escort ..
lemma move_GHplus (r:P→Q)(i:Conn G)(x:P): transport r (GHplus i x)=GHplus i (r x):= escort ..

-- ∆xAt near link. ghosts, chart. and adj s c.
def vel (x : Maurer.Ends G)(i:Conn G)(u:G.Color): ℝ:= Maurer.volts x u i
def steerA (x:P)(i: Conn G)(q: Edge P) (J: Conn G→Maurer.Ends G) : Dot G P:= ∑ j:Conn G,couple DotFlip (GH j x) (onedge q (vel (J j) i))
variable [AddCommGroup P]
def leftStem (i:Conn G): Maurer.Ends G:= (baseC i,0)
def rightStem (i:Conn G) : Maurer.Ends G:= (0,baseC i)
def throat (d:Rail P)(x:Edge P)(i:Conn G): Dot G P:= steerA x.1 i x leftStem + steerA (endRail d x) i x rightStem

def cog (x:P)(i:Conn G): Dot G P := ∑ a:Conn G,∑ b:Conn G,(-(letterLie a b i:ℂ)/2) • couple DotFlip (GH a x) (GH b x)
omit [AddCommGroup P] in
lemma move_steer (r:P→Q)(i : Conn G)(x : P)(q : Edge P) (J:Conn G→Maurer.Ends G) : transport r (steerA x i q J)=steerA (r x) i (r q.1,q.2) J:= by simp_rw [steerA,map_sum, transport_comes,move_GH,onmove]
omit [AddCommGroup P] in
lemma move_cog (r:P→Q)(x:P)(i:Conn G): transport r (cog x i)=cog (r x) i:= by simp_rw [cog,map_sum,map_smul,transport_comes,move_GH]
section finite
variable [DecidableEq P] [Fintype P] (d:Rail P)
local notation "H"=> glow G P
local notation "Y"=> Focus.launch (glow G P) (colorTerm G P) (loco d)
local notation "C"=> panel G P
omit [AddCommGroup P] in
lemma edge_parse (x: Edge P){F:G.Color→ℝ}(h:germ F): (onedge x F).val=reads (fun a:City G P=> F (a x)):= by
   unfold onedge; rw [pooled _ (show germ (fun b:Lot G Unit=> F (b ())) from h.comp (f:=fun b:Lot G Unit=> b ()) 0 (contDiff_apply ..|>.contDiffAt))]; rfl
omit [AddCommGroup P][Fintype P][DecidableEq P] in
lemma gh_letter (x:Eyes G P): (GH x.2 x.1).val= (C).spark x:=rfl
omit [AddCommGroup P][Fintype P][DecidableEq P] in
lemma vel_germ (x:Maurer.Ends G)(i:Conn G): germ (vel x i) := by
   let A:= ((baseC.toBasis).coord i).toContinuousLinearMap; rw [show vel x i=A ∘ Maurer.volts x from funext fun y => (by simp [A,baseC,vel])]; exact A.contDiff.contDiffAt.comp 0 (Maurer.home x)
lemma throat_frame (x:Edge P)(i:Conn G): (throat d x i).val=Y ((C).AId (x,i)):= by
   classical
   rw [launch_stone]
   -- ℂ rank analytic sum. consider even if endRail d x equals x.
   let F (y:Conn G)(v:City G P):= vel (leftStem y) i (v x); let Rj (y:Conn G) (v:City G P) := vel (rightStem y) i (v x)
   have hv (f: G.Color→ ℝ)(h:germ f): germ (fun v:City G P=> f (v x)):= h.comp (f:=fun v:City G P=> v x) 0 (contDiff_apply ..|>.contDiffAt)
   let T:= endRail d x
   have h0 (y:P)(q: Conn G) : (H).seed (x,i) ∘ loco d (y,q) = (if y=x.1 then F q else 0)+(if y=T then Rj q else 0):= by
       ext v; change projector (x,i) (loco d (y,q) v)=_; rw [projector_k, Pi.add_apply,consulted]; change Maurer.voltage (v x) _ i= _; rw [show route d x (priv (y,q)) = (if y=x.1 then leftStem q else 0) + (if y=T then rightStem q else 0) by
          have hl (x:P) : priv (y,q) x= if y=x then baseC q else 0:= by rw [priv,Pi.single_apply]; simp [eq_comm]
          rw [routed,hl,hl]; unfold T; split_ifs <;> apply Prod.ext <;> simp [leftStem,rightStem],
         map_add,PiLp.add_apply]; dsimp only; congr! 1 <;> split_ifs <;> first| rfl| simp
   let YL y q:= product DotFlip ((GH q y).val) (reads (F q)); let YR y q:= product DotFlip ((GH q y).val) (reads (Rj q))
   have he (y:P)(q: Conn G): product DotFlip ((C).spark (y,q)) (ink (H).e0 ((H).seed (x,i) ∘ loco d (y,q)))=(if y=x.1 then YL y q else 0)+(if y=T then YR y q else 0):= by
       rw [h0]; split_ifs <;> first | solve | (rw [ink_add (H).e0 (show germ (F q) from hv _ (vel_germ _ _)) (show germ (Rj q) from hv _ (vel_germ _ _)),map_add]; rfl) | (simp; rfl) | simp
   unfold stone throat steerA
   rw [Fintype.sum_prod_type]; simp_rw [he]; simp only [Finset.sum_add_distrib, add_stack, sum_stack, coupled,edge_parse _ (vel_germ _ _)]; congr! 1
   · rw [Finset.sum_eq_single x.1]; simp only; rfl
     · intro i hi hx; simp [hx]
     simp
   rw [Finset.sum_eq_single T]; simp only; rfl
   · intro i hi hx; simp [hx]
   simp
lemma cog_frame (x:P)(i:Conn G) : (cog x i).val=Y ((C).KId (x,i)):= by
   rw [launch_shadow]; unfold cog shadow; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type,story]; rw [Finset.sum_eq_single x]; swap; · intro i hi he; simp [Ne.symm he]
   swap; · simp
   simp only [true_and,sum_stack,smul_stack,coupled]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_eq_single x]; simp only; rfl
   · intro i hi he; simp [Ne.symm he]
   simp
end finite
end YM.MS.Native.Draft
