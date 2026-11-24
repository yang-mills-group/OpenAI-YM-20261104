import YM.AllOrder.Docket.Bow
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "ξ"=> Aux.scope x
local notation "Y₀"=> Body A.Vx
-- retain precise eligible ε (growth window width). Post chosen later.
abbrev ν:= warm U A.step A.rates
abbrev due (A:Aux.Name G P K u x r k U):= betaF G A.whenP P.L
abbrev vol (A: I):= u A.whenP
structure Civil (s:Age→ℝ) : Prop where
   price :∃ P : Teller G, Intake P A.tube A.whenP A.virgin∧ Intake P A.tube A.whenP A.tilt
   sk :∀ i,(0:ℝ)<s i
   handy v (h:v∈Aux.scope x) : Quoted (A.shape v) (s v) (Step.PlanV.authority (Burn.horizon x) v (Step.PlanV.strengthP A.due))
namespace Civil
variable {s:Age→ℝ}{A} (h:Civil A s)
include h
lemma grammar : Burn.Near A.due A.beta:= by obtain ⟨P,h,-⟩:=h.price; have ht:=h.height; obtain ⟨hz,hk⟩:= h.window; rw [A.step] at ht hz hk; change A.due/2≤A.beta at hz; change A.beta ≤ 2*A.due at hk; change 1 < A.due at ht; constructor <;> linarith
lemma size : A.price.B=radiusB A.due := by obtain ⟨P,h,-⟩:= h.price; have hp:= h.sizes; rw [A.step] at hp; exact hp
lemma temp : A.price.threshold=fiery G A.whenP P.L := by obtain ⟨p,h,-⟩:= h.price; have he:= h.received.temp; rw [A.step] at he; exact he
end Civil
variable (W:ι→ Aux.Name G P K u x r k U)
structure Proper (W:ι→Aux.Name G P K u x r k U)(T:Catch.Clock ι): Prop where
   look : Looks G P.L T (fun i=> (W i).whenP)
   load : Lantern.Bolt G P.L u
   legible : ∃ s:Age→ℝ, (∀ j,0 < s j)∧ ∀ᶠ i in T.rail,Civil (W i) s
variable (h:Proper W T)
include h
namespace Proper
variable (C:ChartRatio G) (hc:LocalRatio C)
lemma sail {Y:Type*} (V:Catch.Clock Y) (x:Y→ι)(hV:T.Fare (U:=V) x):Proper (W∘x) V:= by obtain ⟨s,hs,hS⟩:=h.legible; exact ⟨h.look.high V x hV,h.load, s,hs, hV.tends.eventually hS⟩
local notation "Z₀"=> T.rail
lemma starlit : ∀ᶠ i in Z₀, Burn.Near (W i).due (W i).beta:= by obtain ⟨s,h0,h⟩:= h.legible; exact h.mono fun _ hi=> hi.grammar
lemma windowB : ∀ᶠ i in Z₀,(W i).price.B=radiusB (W i).due := by obtain ⟨s,h0,h⟩:= h.legible; exact h.mono fun _ hi=>hi.size
lemma cheap : T.Meter (fun i=> (W i).price.threshold) (-(1/2:ℝ)):= by obtain ⟨s,h0,hx⟩:=h.legible; exact Meter.eq_mem (h.look.bill Rate.flame) (hx.mono fun i hi=> hi.temp.symm)
lemma meter : T.Meter (fun i=>(W i).Θ) (-(1/2)) ∧ T.Meter (fun i=>(W i).Θ⁻¹) (1/2) := h.look.costs (starlit W h) h.look -- parse dot notion
lemma strength : T.Meter (fun i=>(W i).beta) 1:= by apply ((h.look.slow).lscale 4).smaller; filter_upwards [starlit W h] with i hi; rw [abs_of_pos (W i).bpos]; exact hi.2.trans (le_abs_self _)
lemma counts : T.Meter (Name.vol∘W) 0:= h.look.bill h.load.uses
lemma lever : T.Meter (fun i=>(Fintype.card (W i).Vx:ℝ)) 0:= (counts W h).smaller (Eventually.of_forall fun i=>by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact (countsK _ _ (W i).loom.overall).trans (le_abs_self _))
lemma loam : T.Meter (fun i=>(Fintype.card (Site (W i).f):ℝ)) 0:= (counts W h).smaller (Eventually.of_forall fun i=>by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact (W i).loom.finalP.trans (le_abs_self _))
lemma hire (i:Age) : T.Meter (fun j=> Step.PlanV.authority (Burn.horizon x) i (Step.PlanV.strengthP (W j).due)) 0:= h.look.transfer (G:=G) (Burn.first_rate (G:=G) i (Burn.horizon x))
end Proper
omit h
variable (O:ChartRatio G)(hO:LocalRatio O)(D:ℝ)
abbrev wD (A:Aux.Name G P K u x r k U):= wick G P.L D A.whenP
abbrev Omega (A:Aux.Name G P K u x r k U):= eaves G P.L A.whenP
lemma withGap : (warm U A.step A.rates).tables A.tube.high A.data.patch = U.tables r.clip P := by
 let he (Q:Patch)(K':KernelChoices)(n m:Side)(s:StepData n m)(u:Uniform.Before G r.width r.paths Q.J K' (k+3))(hp:s.patch=Q)(h:s.kernel=K') : (warm u hp h).tables r.clip s.patch=u.tables r.clip Q:=by subst Q K'; rfl;
 rw [A.high]; exact he P K _ _ A.data U A.step A.rates

include A in
lemma gap :0< (U.tables r.clip P).gap := by rw [← A.withGap]; exact ((warm U A.step A.rates).receipt A.forest A.choices A.path.choose_spec A.loom.large rfl rfl).1.pos_m -- A unref type?
lemma positive_gap (h:Nonempty I) : 0< (U.tables r.clip P).gap:= by rcases h with ⟨A⟩; exact gap A
lemma wakes0 (i: A.Vx→ℝ) : dotProduct i ((A.Zc 0)⁻¹ *ᵥ i) ≤ ((U.tables r.clip P).gap/2)⁻¹ * dotProduct i i:= by
 rw [← A.withGap]; exact Lapis.wakes _ _ _ _ _ _ _ _ (warm U A.step A.rates) A.loom.large A.path.choose_spec A.he 0 (norm_zero.trans_lt (A.he.x_pos))|>.2.2.1 i
namespace Proper
variable {D O}
include h
lemma wickD (hd:0<D) : Gate T (fun i=> ((W i).Zc 0)⁻¹) (wD D∘ W):= by
 let v:=(U.tables r.clip P).gap; refine ⟨lever W h, ⟨(v/2)⁻¹, Eventually.of_forall fun i=>⟨(show ((W i).Zc 0).PosDef from ?_).inv,wakes0 (W i)⟩⟩,?_,?_⟩
 · exact Lapis.wakes _ _ _ _ _ _ _ _ (warm U (W i).step (W i).rates) (W i).loom.large (W i).path.choose_spec (W i).he 0 (norm_zero.trans_lt (W i).he.x_pos)|>.1
 · exact h.look.bill (Sienna.gen G P.L D)
 by_cases hx:Nonempty I; swap; · intro s v hv; filter_upwards with i; exact (hx ⟨W i⟩).elim
 have hg:= Name.positive_gap (r:=r) hx; intro v b hb; filter_upwards [h.look.tends.eventually (Lantern.walls G P.L h.load (inv_pos.mpr (half_pos hg)) hd b), h.look.same] with i hi hp; rw [hp, abs_of_nonneg measureReal_nonneg, measureReal_compl measurableSet_closedBall, probReal_univ]; apply hi (W i|>.Vx) (((W i).Zc 0)⁻¹) (countsK _ _ (W i).loom.overall) _ (wakes0 (W i)); exact (Lapis.wakes _ _ _ _ _ _ _ _ (warm U (W i).step (W i).rates) (W i).loom.large (W i).path.choose_spec (W i).he 0 (norm_zero.trans_lt (W i).he.x_pos)|>.1).inv -- theorem wakes arity
end Proper
end Name
end YM.AllOrder.Aux
