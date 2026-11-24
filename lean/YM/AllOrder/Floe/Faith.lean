import YM.AllOrder.Floe.Arbor
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent
variable (Γ:ι→ℝ) {q:Clip} {R:ι→PathData G}{L:ι→ℝ}(h : ∀ i,(R i).Bounds q a C (L i)) (g:G.Simple) (Y:Age) (s:Fees) {B:ι→ℝ}
variable {H:ι→Scene G}{V:ι→Layout G}{Q:ι→ Coin}{X:Finset Age}
local notation "e"=> Age.e Y
local notation "t"=> Age.r Y
local notation "Ψ"=> fun i:ι=> ask q (R i) (H i) (Q i) X (V i)
-- `Pointer` to prototype packet with restored curvature.Applying all degree e.Seeded α∗ projection.
structure Beam (X:Finset Age)(V:Layout G)(q:Clip)(W:PathData G)(K:Scene G)(z:Coin)(f r:ℕ)(Q:ℕ→Atom G r)(α:ℝ) :Prop where
 price : r≠2→α=0
 pens : Aero.Capped (ask q W K z X V f- α • (Pace.base q W 0)) r Q

-- `Proceeded` w/o shell horizon record.Fe.
variable (h0:0≤Ω)(hX:∀ i∈X,i.e < Age.e Y)(hh:Spirit Γ q R H s Y a C σ Ω l N B) (hV:∀ i,Legal X (V i))(hv: ∀ i,0<s i)(hp:strict (fun i=> ask q (R i) (H i) (Q i) X (V i)) Y.e) (hx:∀ i,Pace.Valid (H i) N)
variable (ht:∀ i∈X,∃ f:ι→ℝ, CreditF Γ l f∧∀ j,Extra.Iteration.Charged (V j i) (s i) (f j)) (hd:∀ j≤N,Pace.Cost Γ l fun i=> Q i j)(hL:CreditF Γ l L) (hN:Y.e≤N)
local notation "C✪"=> gateE l N
lemma combineCap {s : ℝ} {H Y:Ink.Money.Bills (Coarse G)} {X X' : ℕ→Atom G k} {v S: ℝ} (hx: Pace.mental (fun _ : Unit=>H))(hy:Pace.mental (fun _:Unit=>Y)) (ht:Capped H k X) (hv:Capped Y k X') (h:Quoted X s S)(hu:Quoted X' s v)(hp:0<s): Capped (H+Y) k (Extra.Iteration.join X X'):= by
 intro n; ext1 i; change jet (H n+Y n) _ _=_; rw [jet_add ((hx () n).contDiffAt) ((hy () n).contDiffAt),ht n,hv n]; let a:= Extra.Iteration.join X X'
 rw [show turnSeries a (m:=n)=turnSeries (m:=n) X+turnSeries (m:=n) X' from funext fun x=> action_join hp h.pay hu.pay (input G n x)]; exact (jet_add (turns_analytic _ hp h.pay|>.contDiffAt) (turns_analytic _ hp hu.pay|>.contDiffAt) _).symm
-- extra argument explicit.No need `Sp.Ap.Call small`. Receipts as in Spirit.
include h g h0 hp hx ht hL hV hh hd hN hX hv
lemma pawns : ∃ (ϕ:ι→ℕ→Atom G (t)) (α f:ι→ℝ),Pace.Cost Γ (C✪) α ∧ CreditF Γ (C✪) f ∧ (∀ i,Quoted (ϕ i) (s Y) (B i+f i)∧ Beam X (V i) q (R i) (H i) (Q i) e t (ϕ i) (α i)):= by
 obtain ⟨U,hq,hU,hδ,f,hf⟩:= hh.receipt; let F i:= ask q (R i) (U i) (Q i) X (V i); let Mφ i:= Pace.base q (R i); let F' i:=ask q (R i) (H i) (Q i) X (V i)
 let d:= e; let r:= t; have hs:0<σ:= hh.print.pos; have hℓ: strict F e:= by
    intro i n k hk; unfold F ask; simp only [Pi.sub_apply]; rw [hq k hk i]; exact hp i n k hk -- Constant binder?
 have hr := hh.print; have hm: money Γ (fun i=> F i e) (r-1) C✪ σ:= timing Γ q R L h g s hU X hV (fun i _=>hv i) ht (fun i hp=> hr.spark i (hX i hp)) hr.slant hd hL hs hδ hN
 have hF (i:ι): Admits (F i e):= pose q R L h g hU X hV hℓ i hN
 -- split r=2 for α restore.he_j.
 have hAuth : ∃ (P:ι →ℕ→Atom G (t)) (α φ:ι→ℝ), Pace.Cost Γ C✪ α ∧ CreditF Γ C✪ φ ∧ ∀ i, Quoted (P i) (s Y) (φ i) ∧ (r≠2→α i=0) ∧ Aero.Capped (F i d- α i • (Mφ i 0)) r (P i):= by
    by_cases he:t=2
    · obtain ⟨S,hS⟩:= hh.metric; obtain ⟨α,φ,K,hα,hφ,Hk⟩:= hr.june he ι Γ C✪ (fun i=> F i e) (fun i=> Mφ i 0) S (by unfold r at hm; rw [he] at hm; exact hm) hF (fun i=>spry g q (R i) (h i)) (fun i=>⟨(hS i).1,(hS i).2.1⟩) (fun i=> (hS i).2.2) -- args.spry order
      dsimp only [r]; rw [he]; exact ⟨K,α,φ,hα,hφ,fun i=> ⟨(Hk i).1,(fun h=> (h rfl).elim),(Hk i).2⟩⟩
    · obtain ⟨y,hy,T,hT⟩:= hr.castle (by have hk : 2≤ Y.r:= Nat.le_add_left ..; omega) ι Γ _ (fun i=>F i d) hm hF
      refine ⟨T,(fun _=>0),y,Pace.Cost.fixed _,hy,fun i=>⟨(hT i).1,fun _=>rfl,?_⟩⟩; rw [zero_smul,sub_zero]; exact (hT i).2
 obtain ⟨E,α,d',hα,hf',hE⟩:=hAuth; refine ⟨fun i=> Extra.Iteration.join (f i) (E i),α,d',hα,hf',fun i=> ⟨((hf i).1).join ((hE i).1),⟨(hE i).2.1,?_⟩⟩⟩
 have hu : ask q (R i) (H i) (Q i) X (V i) e-α i • Pace.base q (R i) 0=(U i e-H i e)+(F i e-α i • Pace.base q (R i) 0):= by unfold F ask; simp only [Pi.sub_apply]; abel
 rw [hu]; refine combineCap (X:=f i) (X':=E i) (fun _ n=> ?_) (fun _ n=> ?_) ((hf i).2) ((hE i).2.2) ((hf i).1) ((hE i).1) (hv Y)
 · exact ((hU i|>.rank e hN n).sub (hx i|>.rank e hN n)).read.smooth.contDiffAt.analyticAt
 exact (hF i|>.rise n).sub (analyticAt_const.mul ((base_pose q (R i) (h i) g|>.rank 0 le_rfl n).read.smooth.contDiffAt.analyticAt))
end YM.AllOrder.Floe.Step
