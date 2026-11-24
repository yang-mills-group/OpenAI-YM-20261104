import YM.AllOrder.Wheel.Roll
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
open Aux Aux.Name Push.PriceCompiler Kinetic.Port -- Bench check
namespace Ride
open Aero Sienna Further.PhysicalPeriodLimitF933
variable {r p:Stage} (K) {q:ℕ}{w:ℝ→ℝ} (O:ChartRatio G)(hO:LocalRatio O)
local notation "κs"=> Burn.horizon q
-- Actor.Action.AlphaSchedule.Grow α.Bridge uses $P$ from patch.L.A admissible ∀ Actor Booth. Do not require hall α threshold yet. positions.Condition t∈W.Cash.
namespace Pair
open Aero Step Step.PlanV Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D':RG.Supply.Rolls X.p}(S:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) (hx:4≤x)
local notation "B"=> X.K
local notation "v"=>X.p.profile x
local notation "u"=>X.p.profile y
local notation "K"=>X.p.kernel
set_option quotPrecheck false
local notation "L"=>Mural.sheet X.p D' hx
local notation "LΩ"=>D'.L x
local notation "Art"=>Plateau.Art (G:=G)
local notation "I"=>Card D' S x y hx κs
local notation "D*"=> Income D' S x y hx κs
variable (D') (U:Uniform.Before G (X.p.profile x).width (X.p.profile x).paths (Mural.sheet X.p D' hx).J X.p.kernel (k+3)) (F: Income D' S x y hx (Burn.horizon q))
local notation "Ic"=> Aux.Name G L K w q v k U
local notation "Θ"=>X.O
local notation "Θ'"=>X.oga
variable (A:ι→Card D' S x y hx (Burn.horizon q)) (C:ι→Aux.Name G (Mural.sheet X.p D' hx) X.p.kernel w q (X.p.profile x) k U)
    (h:∀ᶠ i in T.rail, Pact D' S x y hx U (A i) (C i))(he: Proper C T)
local notation "n'"=> fun i=> (C i).c
local notation "t"=> fun i=> (C i).whenP
local notation "H"=> T.Meter
local notation "Λ"=> fun i:I=> i.self.paid
include A h he
lemma cents : H (fun i=>(A i).self.paid) 0:= by
 refine (he.look.transfer (f:=strengthP) (Burn.hats_rate (G:=G))).eq_mem (h.mono fun i hi=>?_); exact hi.paid.symm
lemma exit_s : H (fun i=>(Fintype.card (Primary (C i).c G):ℝ)) 0:= (he.counts C).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact ((Nat.cast_le (α:=ℝ)|>.mpr (Fintype.card_le_of_injective Sum.inl (β:=Uniform.Joint (C i).forest G) Sum.inl_injective)).trans ((C i).loom.overall.trans (le_abs_self _))))
lemma seasons : Civil (u) T (fun i=> (A i).self.south):= ⟨(Λ ∘ A), cents D' S x y hx U A C h he, Eventually.of_forall (fun i=> (A i).self.downCost)⟩
include F
local notation "σ"=> F.σ
local notation "V₁"=> fun i=> vista F.presence (A i)
local notation "Z"=> fun i=> (C i).tag Θ Θ'
lemma leaks (j:ℕ): H (fun i=> F.issue (A i) j) 0:= by
 let hs(j:I):=F.sustenance.due j; rcases j with _|j; · exact (Meter.nil T _).eq_mem (Eventually.of_forall fun j=> (hs _).1.symm)
 rcases j with _|j; · exact (Meter.nil T _).eq_mem (Eventually.of_forall fun j=> (hs _).2.1.symm)
 rcases j with _|j; · apply Clock.Meter.smaller (Clock.Meter.const T (cloak D' x)); exact Eventually.of_forall (fun i=> by rw [(hs _).2.2]; exact (A i).self.bounded.trans (le_abs_self _))
 by_cases hz:j < κs; swap; · exact (Meter.nil T _).eq_mem (Eventually.of_forall fun i=> (F.sustenance.dormant _ _ (by omega)).symm)
 have hr:= bill_transfer (F.sustenance.income j hz|>.grade) (show T.Meter (Λ∘A) 0 from cents D' S x y hx U A C h he); exact hr.smaller (Eventually.of_forall fun i=>(abs_abs _ |>.symm.le))
lemma ritual : Hall T (κs+2) (fun i=>(C i).beta) (F.issue ∘ A):= by
 let hb:= he.meter C; exact ⟨⟨Eventually.of_forall fun i=>(C i).bpos, he.strength C,hb.1,hb.2⟩,fun i _=> leaks D' S x y hx U F A C h he i, Eventually.of_forall fun i=> ⟨(F.sustenance.due _).1, (F.sustenance.due _).2.1⟩⟩
lemma prices : Mosaic T (κs+2) (F.laid ∘ A):= by
 constructor; intro i hi; obtain ⟨f,hf,h'⟩:=F.sustenance.rents i hi; let L':= cents D' S x y hx U A C h he; let S':= fun x=> (S.wage x y κs (D'.L x).val i); let g x:= |Λ (A x)|; let w(j:I):= S' x * authority κs i (Λ j)+f j; have hg : H (w∘A) 0:=by
    let ht:H g 0:= L'.ab; exact ((( ((Clock.Meter.const T 1|>.add ht).pow _).weak (by simp : 0*(↑(level κs i + 1):ℝ)≤0)).lscale _).add (bill_transfer hf.grade L'))
 exact ⟨S.pre κs y i, w ∘ A, (S.shape _).pos _ _, hg,Eventually.of_forall (fun x=> (h' _).pay)⟩ -- type maybe interior
lemma precious : Wire T (n') (κs+2) (Z) (V₁) := by
 constructor; intro j hk; let f i:= n' i; have hi:H (fun i:ι=> ((f i).val:ℝ)) 0:=(he.counts C).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact (C i).loom.step.trans (le_abs_self _)); let p(i:ι):=(F.revenue.b j (A i) (f i))*dearth (σ) (f i);
 have hz(s:ℝ): H p s:= by
    have hf:= (pay_transfer (F.revenue.pay j hk|>.2|>.grade) (show H (Λ∘ A) 0 from cents D' S x y hx U A C h he) hi); apply Clock.Meter.unitPay hf le_rfl (Clock.Meter.smaller (he.look.bill (Rate.cutoff (a:=s) (G:=G) («L»:=(L).L) F.revenue.pos)) ?_); filter_upwards [h] with i hh; unfold dearth; rw [abs_of_nonneg (Real.exp_pos _).le]; exact (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hh.tension) (neg_nonpos.mpr F.revenue.pos.le))).trans (le_abs_self _)
 choose r hr using (fun i:ι=> (show ∃ r:ℝ, Pact D' S x y hx U (A i) (C i)→ Prices (j+2) (p i) (((C i).tag Θ Θ' j ∘ exteriorL G (C i).c) -(vista F.presence (A i) j (C i).c) - fun _=> r) from Classical.byCases (fun h'=> (worth D' S x y hx U F (A i) (C i) h' hk).imp fun i hi _=> hi) (fun h'=> ⟨1,(fun HB=> (h' HB).elim)⟩)))
 exact ⟨p,r,hz,h.mono hr⟩
end Pair
end Ride
end YM.AllOrder.Wheel
