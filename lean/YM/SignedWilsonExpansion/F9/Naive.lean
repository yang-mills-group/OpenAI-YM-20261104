import YM.SignedWilsonExpansion.F9.Lease
/-!
# Budget interface on the register knobs only.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 810000
namespace YM.SignedWilsonExpansion.Commission.Method.Epic
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes Jury Reg
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa
open Stair Tape RateQ
variable {G:Gauge}{n d k e j l v:ℕ} {ι:Type} {L:Filter ι}{q:ι→ℝ}
variable (h:G.Simple)(T:MS_Data G (Position.OpenAxis.Plot (FVA2.Press.portDeck G)))(S:Prescription ( FVA2.Press.portDeck G)) (W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
open Lattice
open Wilson Gauge WardBin WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer Asymptotics
variable {K':∀ h,Rays G h W.hol}{F:Labels.Frames G}{Ω:Council F}{E:Credit} {R:Realm G (e+1) E} (q':ι→ Epic W F K' Ω R d k v) (p:ι→ (x:Query)→ Sample x.1)
abbrev gallery (p:ι→(x:Query)→ Sample x.1)(d:ℕ)(i:ι) (x:Query): Tape.Table (Normalize.Sec G d) x.1:= numeral W K (p i x) d
local notation "Rθ"=> gallery W K p d
local notation "X'"=> Epic W F K' Ω R d k v
local notation "τ"=> ((n+1)*k)
-- Order scope: `Spring` etc one wallet. permits & separation built later on cutsY.
structure Opt (p:ι→(x:Query)→Sample x.1) (a:Finset Query)(L:Filter ι) (q:ι→ℝ): Prop where
     metrics : Expense.Stretched L (fun i=> (q' i).mesh)
     seats : ∀ᶠ i in L, (q' i).Z ≤ q i
     cardinal (x:Query) : Tendsto (fun i=> p i x) L (Gate x.2.val)
     paid (n:ℕ)(x:Stage (n+1)): (Sigma.mk _ x)∈ a→ (n+1)*d ≤ v ∧
         ∃ U U':Credit,SpringD R ((n+1)*k) 0 v U∧ Dormitory R ((n+1)*k) 0 U' ∧ ∃ t:ℝ,0<t ∧ ∀ᶠ i in L, Look W (q' i) t (p i (Sigma.mk _ x))
lemma Opt.max {a}:∀ U:Opt W q' p a L q, Maxer L q:= fun x=> x.seats.mono fun i h=> (( (q' i).paid.charm d le_rfl ).pos).trans h
include M h
lemma Opt.fac (a:Finset Query)(V:Opt W q' p a L q): Faculty W K ( F.level d ) ( fun i=> tenor W P' (q' i) ) (fun i=> voice W K (q' i)) ( Rθ ) L q a e:=by
    let Y(i):=voice W K (q' i); refine ⟨fun _=> verso_zero .., fun _=> verso_real .., fun i j=> (q' i).paid.custody .. , ?_, V.max _ _ _ , ?_⟩
    · intro i k t; exact ( Method.ears h T S W K M _ i.2.property k t ).comp (V.cardinal i)
    intro i u f j h0; rcases i with ⟨_|n,x⟩
    · exact Billed.via (Billed.const _) (Eventually.of_forall fun i=> congr_arg (coeff j) (vacuum_t W K _ _ _ (verso_zero ..))) -- param
    obtain ⟨hv,U,U',ht,hw,t,h',hV⟩:=V.paid n x u; have he:= (P'.nested_solution W d V.metrics).2; obtain hp1:= (goesFront V.metrics).eventually (Rose.usable W K h); unfold Billed BoundPoly; let τ':=(n+1)*k; let Z(i):= (q' i).Z
    let C:= lightFee W.hol F Ω d k v e; let Q:= (C.powC (n+1)).prodC (Shard.pur (coinMat τ' e ^ n)); let V':= (cabin G τ' e 0 E U').prodC (Q.prodC (Credit.leanC.powC ((n+1)*d))); let Z':=(FitsZ.hairC G e E).prodC (bosun F W.surveys K' d k n e v); let T':=Z'.plus ((LampTax G n k e v E U U' C t).plus V'); refine ⟨T',?_⟩; filter_upwards [V.seats,he,hp1,hV] with i hi he hv' hh; exact ((pension W K (q' i) t _ hh he.1 hv' hv f h' U U' ht hw) j h0).trans (T'.elder ( ( (q' i).paid.charm d le_rfl).pos ) hi)
-- final estimate evaluation at ℓ frame and Clock
lemma scholar (s:Axis)(u:6≤d)(A: Opt W q' p (Query.crew h T S W K M s d u) L q) : Costy L q (fun i=> voice W K (q' i)) e ∧ ∀ k≤e, Across L q ℂ (fun i=> tenor W P' (q' i) k):=by
    have he:= pacing h T S W K M q' A.metrics (A.fac h T S W K M _ _ _) u s (le_refl _); exact ⟨fun i hi=> he.zen i (Nat.lt_succ_of_le hi),fun i hi=> he.older i (Nat.lt_succ_of_le hi)⟩
end YM.SignedWilsonExpansion.Commission.Method.Epic
