import YM.MSbar.Lease.Angle
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {U:Config G f}{R: Rep G f}{R':Rep G c}{σ C T K B a b v r δ w β u:ℝ}{M k m:ℕ}
open ConnectedActivityE6 Finset RG.PathData Tree Push.Uniform Pressure SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric Posture
variable (P:Patch)(D:KernelChoices)(p:Palisade)(J:Voice G) (L L' : Stage)
set_option quotPrecheck false
local notation "Ξ"=> tip G P.L
variable (G)
def matter (τ:ℕ→ℝ→ℕ):= τ -- unused
lemma Beads : Beam G P.L (fun x=> (voyageB (tip G P.L x):ℝ)) :=by
    let v(x:ℝ):= (radiusB (tip G P.L x):ℝ); have hv:= Beam.shore P.L G; unfold voyageB; push_cast
    exact (((((Beam.coin 4).mul hv).add (Beam.coin 2)).mul (hv.add (Beam.coin _))).add hv).add (Beam.coin _)
variable (f:ℝ→ℕ)(hF: Beam G P.L (fun x=>(f x:ℝ)))
def carpet (L:Stage)(x t:ℝ)(y:ℕ):=
    let b:=L.width; let p:=L.paths; let R:=radiusB x; let u:=voyageB x
    craft p b t y u
include hF
lemma plumet : Pole G P.L (fun x=> Heath.cape (f x) L.width (voyageB (Ξ x))) := by
    let d:= L.width; let b:= tip G P.L; let k(x:ℝ):=voyageB (b x)
    have hP :Pole G P.L (fun x=> Real.exp (-d/2*k x)):= by
       have hD:= half_pos L.width_pos
       apply (Pole.cape P.L G hD).lower; refine Eventually.of_forall fun x=> ?_; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _),neg_div]; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos_of_nonneg hD.le); apply Nat.cast_le.mpr
       unfold k voyageB; dsimp only; have he : radiusB (Ξ x) = radiusB (b x):=rfl; rw [he]; omega
    have ht := Beads G P; unfold Heath.cape; exact (hP.mul hF.tick).mul ((((Beam.coin 2).mul ht).add (Beam.coin 1)|>.power 4).add (Beam.coin _)|>.tick)
lemma lux : Pole G P.L (fun x => carpet L (Ξ x) (2*Ξ x) (f x)):=by
    unfold carpet craft
    let b x:=2*Ξ x*(16*L.paths^2*Fintype.card PlaqAxes+L.paths*(crownAtom L.width 3+crownAtom L.width 4))
    let H x:=Heath.cape (f x) L.width (voyageB (Ξ x)); have hv := (plumet G P L f hF).mul (show Rate G P.L 1 b from ((Rate.hat (G:=G) (L:=P.L)).mul_left _).mul_right _) -- whitespace
    apply hv.lower; exact Eventually.of_forall (fun x=>by change |b x*H x|≤ |H x*b x|; rw [mul_comm (b x)])
-- perhaps implicit alphabetical. macroR1
variable (G0:Gauge)
def woolLease (L:Stage)(x β:ℝ)(n:ℕ) := let v:= voyageB x; let k:= L.supportExponent; let r:=4* radiusB x+2; let b:=L.width; let a:=k/2; let K:=radiusB x; 2*carpet L x β n +2*lbt x*crownAtom b 2* Heath.cape n b v + (4*Real.exp (100*a)*Real.exp (-a*K))*n*((2*(r:ℝ)+1)^4*meter a)*ability x
lemma status : Pole G P.L (fun x=> woolLease L (Ξ x) (2*Ξ x) (f x)):=by
    let a:=L.supportExponent/2; have hh:= lux G P L f hF; let r(x:ℝ):=((4*radiusB (tip G P.L x)+2:ℕ):ℝ); let b:=L.width; let w x:=2*lbt (Ξ x)*crownAtom b 2
    have hr :Beam G P.L r:=by unfold r; push_cast; exact ((Beam.coin 4).mul (Beam.shore P.L G)).add (Beam.coin _)
    have ha: Rate G P.L 0 w:=(((show Rate G P.L 0 (lbt ∘ Ξ) from Rate.monitor.mul_left (2:ℝ)).mul_left 2).mul_right _)
    have hx:= (plumet G P L f hF).mul ha
    let k x:=Real.exp (-a*(radiusB (Ξ x):ℝ)); have hK:=Pole.cape P.L G (half_pos L.price_pos)
    let u x:=(2*r x+1)^ (4:ℕ)*meter a; have he: Beam G P.L u:= ((((Beam.coin 2).mul hr).add (Beam.coin 1)).power 4).mul (Beam.coin _); let v x:= Heath.cape (f x) L.width (voyageB (Ξ x))
    let J x:=4*Real.exp (100*a) *k x*(f x)*u x * ability (Ξ x); have hL:Pole G P.L J:= ((Pole.mul (f:=fun i=>4*Real.exp (100*a)*k i) (fun i=> (hK i).mul_left _) hF.tick).mul he.tick).mul (ability_rate G P.L)
    intro i; apply Rate.congr (((hh i).mul_left 2).add (hx i)|>.add (hL i)); refine Eventually.of_forall fun x=> ?_; change _ = 2*_+v x*w x+J x; rw [mul_comm (v x) (w x)]; rfl -- maybe goal orientation
omit hF in
lemma Pole.error {w:ℝ→ℝ}(h:Pole G P.L w): Pole G P.L (fun i=> Real.exp (w i)-1) := by
    apply Stock.Pole.lower (f:=fun x=>4*w x) (fun i=>(h i).mul_left 4)
    filter_upwards [(h (-1)).below (by norm_num) 1 zero_lt_one] with x hx
    let f(y:ℝ):=Real.exp y-1
    have hb(z:ℝ)(hv:z∈closedBall (0:ℝ) 1) : ‖deriv Real.exp z‖≤4:=by simpa only [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_pos _|>.le)] using ((Real.exp_monotone (show z≤1 from (le_abs_self _).trans (by simpa using hv))).trans (by linarith [Real.exp_one_lt_d9]))
    have ht := (convex_closedBall (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le (fun y h=> Real.differentiable_exp y) hb (mem_closedBall_self zero_le_one) (mem_closedBall.mpr (show dist (w x) 0 ≤ 1 from by simpa using hx)); simpa [abs_mul] using ht
end YM.MSbar.Heath.Cottage
