import YM.LocalLTE.River.Work
/-! ## Inherited stains on precisely the REAL layout -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Turf
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}{B:BudgetPoint}{X:Support c}{f:Config G c→ℂ} {o:Site c}
variable (g:G.Simple) {M : Metals G} {D:Rolls M.p} {A:Alloy M D}
    {R: Factor A} {l v:ℝ} {N m n k d:ℕ} (hm:m<N) {Z:Bolt A} (h: HasSlots ((Issue.trail Z).rep N n m).p ((Issue.trail Z).rep N n m).activities) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "L₀" => D.L j₀
local notation "f₀"=> A.B.a.clock.hatBeta m
local notation "P" => M.p.profile i₀
local notation "pT" => R.prices j₀ i₀
local notation "S0" => ships A.B N m n
local notation "N'" => A.B.a.clock.op m n
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "U!" => ((H).rep N n (m+1))
local notation "O'" => ((H).rep N n m)
local notation "ip"=> A.B.a.params m
variable (hC:Mallow.Arrives R.shape A.delay) (hM : Graces.Moms R.prices M.K R.span M.p.floorL)(hV: Graces.Cruise R.prices D R.recordP R.span R.shape A.delay) (hd:d+3 ≤ A.B.a.clock.J m) {K:ℕ → ℝ}{W:Bid.Worth}(hp : Doors.Budget A.B.a K W)(hh : Graces.Comply R.shape A.delay)
variable (U : Turf R N m n)
    (hr : (Issue.trail Z).rep N n (m+1)= U.inPort) (hℓ: (Issue.trail Z).rep N n m=U.output) (hΘ:HasSlots U.inPort.p U.inPort.activities)
open YM.MergeProof
local notation "R'"=> U.inPort
local notation "tu"=> localSection G d
set_option quotPrecheck false
local notation "V!"=> U.door
local notation "sandbox"=> U.houseB
local notation "Rπ"=> duet _ _ _ _ hℓ hr V!
local notation "cX"=> A.B.a.S.side (m+1) n
local notation "z'"=> (((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d)
local notation "δ"=> (Real.sqrt (A.B.a.clock.forcedAllowance m))
local notation "Xa" T => Blush.scope U.houseB (T) (0:Site (A.B.a.S.side m n))
local notation "P'" T => Blush.screen U.houseB T (U.lamp (T|>.live)) (U.lamp (T|>.pale)) ((((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d)) ((Labels.frames G).level d)
local notation "Bu" C=> Blush.fields (sandbox) C z'
local notation "F" => ((Labels.frames G).level d)
-- Pricing germ entry uses only supported terms
variable (C C' S:Cloud U.inPort)(hk:C'.live.turn=C.live.turn) (hv: S.live.turn=C.live.turn)
variable (ℓ:ℕ)(h0:0∈ C.live.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "Ya" C => LocalLTE.Dilation.silhouette (0:Site (A.B.a.S.side m n)) B ℓ (Xa C)
include hk
lemma poses : (Ya C') = (Ya C):= by rw [LocalLTE.River.scope_eq U C C' hk]
include hm hC
variable {w y ξ:ℝ}
open YM.LocalLTE.Vinca
lemma rework (hF:∀ V,LocalLTE.River.bulk C V=LocalLTE.River.bulk C' V)
    (hp0:Planned.GuardedAtom.Deck (P' C') 0 (Xa C') U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) y w): Planned.GuardedAtom.Deck (P' C) 0 (Xa C) U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) y w:=by
    let Df := P' C; let Di:= P' C'; let S: Unit→Cloud U.inPort:= fun _=> C'; let z:Unit→ℂ:=fun i=> 1
    have h V: LocalLTE.River.bulk C V=∑ i,z i*LocalLTE.River.bulk (S i) V:=by rw [hF]; simp [z,S]
    obtain ⟨x,hx,hU⟩:=hp0.bulk; have ht := hp0.packets
    rw [LocalLTE.River.scope_eq U C C' hk] at hx hU
    have hL:Df.forced=Di.forced:=by funext i V; simpa only [z,S, Fintype.sum_unique, one_mul] using! LocalLTE.River.tintK U z' C (fun i=>hk) h (F) i V
    refine ⟨⟨x,fun i=> ?_, hU⟩,?_⟩
    · have hc := hx i; refine ⟨hc.1,fun V hV l hl hv=>?_⟩
      have hh:Df.bulk i ∘ increment V =ᶠ[𝓝 0] Di.bulk i ∘ increment V:=by filter_upwards [LocalLTE.River.tintE hm U z' C (fun i=> hk) h (F) hC i V hV] with Z hZ; simpa only [z,S, Fintype.sum_unique,one_mul] using! hZ
      change ‖leftDerivs (Df.bulk i) l V‖≤_; rw [Local.left_congr _ V hh]; exact hc.2 _ hV l hl hv
    change Push.Local.ForceCost _ _ Df.forced _; rw [hL];exact ht
omit hk
include g in
lemma enlargementQ (hp0:Planned.GuardedAtom.Deck (P' C) 0 (Xa C) U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) y w) (hi: (0:Site (A.B.a.S.side m n))∈ C.live.crest.image (A.B.a.clock.op m n).ratio.parent): Patched U.output.p 0 (Ya C) ((P' C).bulk) (LocalLTE.Dilation.sill (A.B.a.budget m).supportExponent ℓ * y):=by
   obtain ⟨x,hx,hU⟩:= hp0.bulk; have he:= (U.lightB g hm hC C 0 z' (localSection G d) hi).1; have hv := LocalLTE.Dilation.roomy (0:Site (A.B.a.S.side m n)) B ℓ (Xa C)
   let s:=LocalLTE.Dilation.sill (A.B.a.budget m).supportExponent ℓ; have hX:= Local.sumBudget_mul_left hU (zero_le_one.trans hv.factor)
   exact ⟨x, Local.sumBudget_mono hX (fun i=> mul_nonneg (Real.exp_pos _).le ((hx i).1)) (fun i=> hv.charges _ _ ((hx i).1)) le_rfl,fun i=> ⟨regular_larger (he.regular i) (hv.broad _), bound_larger (hx _) (hv.broad _)⟩⟩
include g h0 hk hv
open YM.LocalLTE
local notation "S'"=> LocalLTE.Dilation.sill (A.B.a.budget m).supportExponent ℓ
-- analytic projection. Integrability only needed on sold arcs.
lemma staysQ (hF:∀ V,River.bulk C V=River.bulk C' V+ River.bulk S V)(E:ℕ→ Config G (A.B.a.S.side m n)→ℂ)
    (hp0: Planned.GuardedAtom.Deck (P' S) 0 (Xa S) U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) y w)
    (hH:Patched U.output.p 0 (Ya C') ((Bu C')-E) ξ): Patched (A.B.a.budget m) 0 (Ya C) ((Bu C)-E) (S'*y+ξ):=by
    let Y:= (Ya C); let D₁:= P' C'; have h (S:Cloud U.inPort)(h:S.live.turn=C.live.turn):0 ∈ S.live.crest.image (A.B.a.clock.op m n).ratio.parent:= by rw [show S.live.crest=C.live.crest from congr_arg (fun v=> v.support U.inPort) h]; exact h0
    have he(Z:Cloud U.inPort)(hZ:Z.live.turn=C.live.turn) i : (A.B.a.budget m).Regular ((Ya C) i) ((P' Z).bulk i):=(by rw [← poses U C Z hZ ℓ]; exact regular_larger ((U.lightB g hm hC Z 0 z' (localSection G d) (h Z hZ)).1.regular i) ((LocalLTE.Dilation.roomy 0 B ℓ (Xa Z)).broad i))
    have ht := enlargementQ g hm hC U S ℓ hp0 (h S hv) -- order
    rw [U.poses C C' hk ℓ] at hH; rw [U.poses C S hv ℓ] at ht
    obtain ⟨j,hJ,hj⟩:= ht.permit; obtain ⟨k,hK,hk'⟩:= hH.permit; let a:=fun i=> j i+k i
    refine ⟨a, ?_, fun i=>?_⟩; · simpa only [a,Local.reservedMass,mul_add] using! Local.sumBudget_add hJ hK
    have he1:= hj i; have he2:=hk' i
    have hR:(B).Regular (Y i) (E i):= sub_sub_cancel ((Bu C') i) (E i) ▸ Next.Foundations.regular_sub (he C' hk i) (show (B).Regular _ ((Bu C') i-E i) from he2.1)
    let f:= ((Bu C) i - E i); let u':=(Bu S) i+ ((Bu C') i-E i); have hL : (B).supBounds 0 (Y i) u' (a i):= bound_add he1.1 he2.1 he1.2 he2.2
    refine ⟨Next.Foundations.regular_sub (he C rfl i) hR, hL.1,fun V hV l hl hv' =>?_⟩
    have hV:Healthy U.output.p.threshold ((Xa C) i) V:= Finset.disjoint_of_subset_left ((Dilation.roomy 0 B ℓ (Xa C)).broad i) hV
    let T : Bool→Cloud U.inPort:=fun i=> if i then C' else S; let s:Bool→ℂ:=fun _=>1
    have hS i:(T i).live.turn = C.live.turn:=by cases i; exact hv; exact hk
    have hr v:River.bulk C v=∑ i,s i*River.bulk (T i) v:=by rw [Fintype.sum_bool, hF]; simp [T,s]
    have hh:= River.tintE hm U z' C hS hr F hC i V hV -- worry F notation
    have h:f ∘ increment V =ᶠ[𝓝 0] u' ∘ increment V:=by
       filter_upwards [hh] with z hz; simp only [s,T, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,one_mul] at hz
       unfold f u'; simp only [Pi.add_apply,Pi.sub_apply, Function.comp_apply]; change (Bu C) i (increment V z)= (Bu C') i (increment V z)+(Bu S) i (increment V z) at hz; rw [hz]; abel
    change ‖leftDerivs f l V‖≤_; rw [Local.left_congr _ _ h];exact hL.2 V (show Healthy _ _ V from by assumption) l hl hv'
end YM.PhysicalNext.Repeat.Mallow.Turf
