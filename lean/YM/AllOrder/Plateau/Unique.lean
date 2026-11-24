import YM.AllOrder.Plateau.Bank
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
section know
open Kinetic.Port
variable (P:Patch)(K:KernelChoices){a Λ:ℝ}
local notation "S[" n "]"=> dock P K n
variable (O:ChartRatio G)(hO:LocalRatio O)
set_option quotPrecheck false
local notation "L"=>P.L
-- P only Kernels. horizon A family includes Wilson geometry, paths immutable & request on any n, alpha leader etc.
variable (p q:Stage) (B:ℝ) (v:ℕ)
local notation "a₁"=>p.paths
local notation "a₂"=>q.paths
local notation "p'"=>p.clip
local notation "q'"=>q.clip
open Further.PhysicalPeriodLimitF933 Macrame
-- ℝ≤ B. Pressure.Channels aux helper. Param present at each Booth proof; rho ext transport.
local notation "I"=>Ticket P K O p q B
variable {P K O p q B} {B':ℝ} (F:Folio P K O hO p q B N) (U:Folio P K O hO p q B' j) (i:Ticket P K O p q B)(u:Ticket P K O p q B')(hp:u.north=i.north)
-- witness changes kernels receipts; canonical set/p repr unique modulo unit
abbrev membrane (k:ℕ) (n:Side)(x:rule (Coarse G) n):= topiary P K p.clip O Ticket.north Ticket.paid F.grant Ticket.upCost hO F.forms F.code k i n x
local notation "M"=> membrane hO F i
local notation "M'"=> membrane hO U u
variable (hk:k≤N)(hi:k≤j)
local notation "Y"=>rule (Coarse G) n
include hp
lemma membrane_unique (h:Ad G P K n) (x y:Y) : M k n x-M k n y=M' k n x-M' k n y := by
   -- equal level, independent intensive price.Unit. accounts.P.
   
   let H':= startup (trees P K n) O (label S[n]) i.north p.clip F.grant h i.upCost (F.code i n h) hO; let H:= startup (trees P K n) O (label S[n]) u.north p.clip U.grant h u.upCost (U.code u n h) hO
   let f(y:Y):= ratePlan H' k (exteriorL G n y); have hx(w:Y):f w= just (preview H') k+membrane hO F i k n w:= by
      let a(x:Ticket P K O p q B):=x.north; let hh: Nonempty (Ticket P K O p q B):=⟨i⟩; exact actual_top P K _ _ _ _ _ _ _ _ F.code _ _ h w
   have hh(w:Y):f w= just (preview H) k+membrane hO U u k n w:=by
      have hh: Nonempty (Ticket P K O p q B'):=⟨u⟩; have hx(V:Y):= actual_top P K _ O _ Ticket.paid _ Ticket.upCost hO _ U.code u _ h (k:=k) V
      refine Eq.trans (b:=ratePlan H k (exteriorL G n w)) ?_ (hx _); unfold f; let W:= i.north; have he:0<H'.paid 0:=mul_pos (pow_pos hO.scale _) (Real.exp_pos _); have hg:0<H.paid 0:=mul_pos (pow_pos hO.scale _) (Real.exp_pos _); let A:= primitive (f:=Progress.ClassicalKin.Tent.below P n) u.north p.clip; let C := primitive (f:=Progress.ClassicalKin.Tent.below P n) i.north p.clip; have hp':A=C:=congr_arg (fun w:PathData G=> primitive w p.clip) hp; have ht a : Toll _ (A a):=(toll_main u.upCost).add ((toll_loop u.upCost).scale (a^2));
      let F₀:= trees P K n; let T:=dock P K n; let l:= label S[n]; have hr (A C:ℝ→ Config G (Progress.ClassicalKin.Tent.below P n)→ℝ)(Ξ:Desk F₀ O C l)(G':Desk F₀ O A l)(he:0<Ξ.paid 0)(hg:0<G'.paid 0)(ht:∀ z,Toll _ (A z))(hQ:A=C): ratePlan Ξ=ratePlan G':= by subst A; exact Response.exactly _ _ he hO h.1 ht hg
      exact congr_fun (congr_fun (hr A C H' H he hg ht hp') _) _
   linarith only [hx x,hx y,hh x,hh y]
variable (hB:P.Branches K G)
omit hp
include hk hB in
-- single version 𝓣:Tendsto.Bind. available by M_lit.
lemma asserts (x:Y): Tendsto (fun i':ℕ=> ((↑((i'+1)^4:ℕ):ℝ)⁻¹)* M k (Ink.Echo.amplify n i') (convey (Ink.Echo.arm n i') x)) atTop (𝓝 ((F.presence k i).table n x)) := by -- edit
   obtain ⟨a,h,t,h'⟩:= F.well.fee k hk; exact Ink.Echo.transported (Ink.Echo.arm n) (h'.awake i) (Ink.Echo.scaleLean h'.story i) (Ink.Echo.limitless n) h'.berth (dock_larger P K hB) (fun i=> by positivity) _ (Ink.LinTest.eval _ x)
include hB hk hi hp
lemma uniquely : Shellac.off ((F.presence k i).table n)= Shellac.off ((U.presence k u).table n):= by
 ext1 y; apply tendsto_nhds_unique_of_eventuallyEq ((asserts hO F i hk hB y).sub (asserts hO F i hk hB (0:Y))) ((asserts hO U u hi hB y).sub (asserts hO U u hi hB (0:Y))); obtain ⟨b,H⟩:= dock_larger P K hB; filter_upwards [(Ink.Echo.limitless n).eventually (eventually_ge_atTop b)] with i' hi;
 set e:= ((↑((i'+1)^4:ℕ):ℝ)⁻¹); let T':= Ink.Echo.amplify n i'; change ((↑((i'+1)^4:ℕ):ℝ)⁻¹)*_- ((↑((i'+1)^4:ℕ):ℝ)⁻¹)*_= ((↑((i'+1)^4:ℕ):ℝ)⁻¹)* _- ((↑((i'+1)^4:ℕ):ℝ)⁻¹)*_; rw [← mul_sub,←mul_sub]; exact congr_arg (fun g=> ((↑((i'+1)^4:ℕ):ℝ)⁻¹)*g) (membrane_unique hO F U i u hp (H _ hi) _ _)
lemma recur_unique (he:u.south=i.south)(h:u.alpha=i.alpha): crowd F.reps (N+1) i k n= crowd U.reps (j+1) u k n:= by
 let A:= ((F.presence k i).table n+Stipend q.clip i.south i.alpha k n); let D:= ((U.presence k u).table n+Stipend q.clip u.south u.alpha k n); let a x:= crowd F.reps (N+1) i k n x; let v x:= crowd U.reps (j+1) u k n x;
 have heq(x:Y):A x-A 0 =D x-D 0:= by unfold A D; rw [he,h]; simp only [Pi.add_apply]; have ht:=congr_fun (uniquely (n:=n) hO F U i u hp hk hi hB) x; unfold Shellac.off at ht; simp only [Pi.sub_apply] at ht; linarith only [ht]
 have ht {ι:Type}(F:Repertoire ι G)(u:ι)(k j:ℕ)(n:Side):crowd F k u j n 0=0:= by
     unfold crowd; simp_rw [Finset.sum_apply,Haiku.Coat.reel,Finset.sum_apply]; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro i _; unfold trade; split
     next h=>
         have hH: j-a+(i.val+2) ≠ 0:=by omega
         unfold jet; rw [ContinuousMultilinearMap.map_coord_zero _ (⟨0, Nat.pos_of_ne_zero hH⟩ : Fin (j-a+(i.val+2))) rfl, mul_zero];
     next => rfl
 ext1 x; have hx:A x-a x=A 0-a 0:=F.splice.project i n k (Nat.lt_succ_of_le hk) x 0; have hh:D x-v x=D 0-v 0:=U.splice.project u n k (Nat.lt_succ_of_le hi) x 0; have hu : a 0=0:= ht ..; have hy: v 0=0:=ht ..; change a x=v x; linarith only [hx, hh, hu,hy,heq x]
end know
end YM.AllOrder.Plateau
