import YM.FVA2.Cure
/-!
# Actual normalization on point supplier and cancellation even under continuous-center support.

No estimates carried through the ill-conditioned preperiodic operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector PositionX.Bend
open Lattice Topology Elegant
open MS MS.Menus MS.Land MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Counterpart
open Fountain PayAll
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(hg:G.Simple){B:Booked (wings G)} (V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G B)
variable (H:ExactSpin V P)(HI:Trusted P)(he: MixedStory.AllProfiles M V P) (q:ℕ+)(hq:1<q.val)(μ:ℝ) {d n:ℕ}
local notation "Y"=> V.F
local notation "ℙ"=> BoxOffice.warehouse V
local notation "δ"=> nested V.F hg (BoxOffice.warehouse V)
local notation "𝒮"=> Spring.ms V M μ
local notation "F"=> (atTop:Filter ℕ)
local notation "W"=> Bank V.F d
local notation "E₀"=> E V.F d
local notation "Ξ"=> (𝒮 d)
variable {c:ℝ}(T:Booth c V.F)(Z:Knocker hg T q hq (warehouse V))
open PertExtension.LatticePT (side epsilon origins Grid.sample)
open Prow
section similar
variable {I:Type*} {l:Filter I}{q:I→ℝ}{F': Labels.Frames G}
variable {A B:I→ PayAll.reprK F' d n}{L: PayAll.reprK F' d n}
abbrev Similar (l:Filter I)(q:I→ℝ)(A B:I→ PayAll.reprK F' d n)(L: PayAll.reprK F' d n):Prop:= ∀ p:Fin n→ E F' d,Prow.side l q (fun i=> taste ( A i ) p) (fun i=> taste ( B i ) p) ( taste L p )
lemma Similar.gold (h:Rag l q)(hp:Similar l q A B L): Prow.Gold l q (fun i=> keynote ∘ A i) (fun i=> keynote∘ B i) ( keynote ∘ L ):= by
    intro ⟨m,p,v⟩ t; change Tandem _ _ (fun i=> keynote ( A i t ) m v p) (fun i=> keynote ( B i t ) m v p ) (keynote ( L t ) m v p); by_cases hm:m=n; · subst m; simp_rw [show ∀ u:PayAll.hall F' d n,keynote u n v= u from ( heap · v )]; exact hp _ _
    simp_rw [ keynote, dif_neg hm ]; exact Tandem.stable h _
lemma Similar.res {X Y':I→Word (Buffer F' d)} {Z0: Word ( Buffer F' d )} (h:Rag l q)(hp:Similar l q A B L)(hv:Prow.side l q X Y' Z0): Similar l q (fun i=> heated ( A i ) ( X i )) (fun i=> heated ( B i ) ( Y' i )) ( heated L Z0 ):= fun i n=> ( hp.gold h ).shop h hv ⟨ _,i,0 ⟩ n
lemma Similar.renU {X Y':I→Word ℝ} {Z0: Word ℝ} (h:Rag l q)(hp:Similar l q A B L)(hv:Prow.side l q X Y' Z0): Similar l q (fun i=> ren ( X i ) ( A i ) ) (fun i=> ren ( Y' i ) ( B i )) ( ren Z0 L ):= by
    intro p; simp_rw [ value_ren ]; exact (hp _).twistS h hv
lemma Similar.congr {C:I→ PayAll.reprK F' d n}(h:A =ᶠ[l] C)(hp:Similar l q A B L): Similar l q C B L:= fun p i=> (hp p i).congr (h.mono fun _ ht=> congr_arg ( fun F' => PayAll.taste F' p i ) ht)
end similar
section point
variable {I:Type*}{l:Filter I} {f:I→ℕ}(h:Tendsto f l atTop) (O:(i:I)→ Lattice.Site (PertExtension.LatticePT.side q ( f i ))) (U:(i:I)→ Fin n→ Lattice.Site (PertExtension.LatticePT.side q ( f i ))) {R:Set (Points n)}
local notation "Zx" i=> ( Grid.sample q ( f i ) ( U i ) )
local notation "χ"=> isell hg V P H HI q μ T
local notation "ψ"=> ξ hg V M μ T
variable (hO:∀ᶠ i in l,O i∈ PertExtension.LatticePT.origins q ( f i )){x:Points n}(hx:R ⊆conf n)(hR:IsCompact R) (hY: x∈R)(hW:∀ᶠ i in l, Grid.sample q (f i) (U i)∈R ) (hU:Tendsto (fun i=> PertExtension.LatticePT.Grid.sample q (f i) (U i)) l (𝓝 x))
include h hO hU hW hY hR hx Z he H HI
local notation "η"=> feel q
lemma shape_power (d:ℕ) : Similar l (η ∘ f) (fun i=>counter hg V q (f i) T (O i) ( U i ) d ) (fun i=> trueK hg V M μ T ( Zx i ) d ) ( trueK hg V M μ T x d ):= by
    obtain hη:=fading_t q hq h; have hp: Similar l (η ∘ f) (fun i=> sounded V P H HI q μ (f i) ( O i ) ( U i ) d) (fun i=> phy V M μ ( Zx i ) d) (phy V M μ x d):= by
         intro p n; refine ⟨?_, ( Fountain.shapes V M n μ x p (hx hY) ).tendsto.comp hU ⟩; obtain ⟨ C,hC,hV⟩:= Fountain.rate_point V P M H HI he q hq μ hx hR n p; refine ⟨ C,hC,?_ ⟩; filter_upwards [h.eventually hV,hO,hW] with i hi ho hw; exact hi _ ho _ hw
    have ht:= hp.res hη ( report_power hg V P M H HI he q hq μ h d ); have hv:= ht.renU hη (inverse_power hg V P M H HI he q hq μ h T Z); refine hv.congr ?_; filter_upwards [ h.eventually ( movement hg V P M H HI he q hq μ T Z d ), h.eventually ( meterLive hg V P M H HI he q hq μ T Z |>.1 ) ] with i hi hk; change ren ( inverse (χ ( f i )) ) ( projected hg V P H HI q μ _ _ _ _ ) = _; rw [( hi n _ _ ).2 ]; ext1 z; ext1 p; change PayAll.taste (ren _ _ ) p z=_; rw [ value_ren,value_ren, asc (lives _) hk.1,guarded hk,ren_head ]
omit h hO hU hW hY
local notation "site" j=> Lattice.Site (PertExtension.LatticePT.side q j)
theorem rate_points (p:Fin n→ E V.F d)(k:ℕ) : ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop, ∀ (u:Fin n→ site i), Grid.sample q i u∈R → ∀ o∈origins q i, dist ( counter hg V q i T o u d k p ) ( trueK hg V M μ T ( Grid.sample q i u ) d k p ) ≤ C*feel q i:= by
    by_contra! h
    have ht (i:ℕ): ∃ j≥i, ∃ (u:Fin n→ site j)(o:site j), Grid.sample q j u∈ R ∧ o∈ origins q j ∧ (i:ℝ)* feel q j < dist ( counter hg V q j T o u d k p ) ( trueK hg V M μ T ( Grid.sample q j u ) d k p ) := by
        obtain ⟨j,hj,v,hv,o,ho,hK⟩:= frequently_atTop.mp ( h ((i:ℝ)+1) (by positivity)) i; exact ⟨ j,hj,v,o,hv,ho,lt_of_le_of_lt (mul_le_mul_of_nonneg_right (show (i:ℝ)≤ (i:ℝ) + 1 from by linarith) ( Fountain.cost_pos _ _|>.le)) hK⟩
    choose F' H' U O hP hc hL using ht; obtain ⟨a,ha,σ,hσ,hZ⟩:= hR.isSeqCompact hP; have hF:Tendsto (F' ∘ σ) atTop atTop:= ( tendsto_atTop_mono H' tendsto_id ).comp hσ.tendsto_atTop; obtain ⟨c,hK,hV⟩:= shape_power hg V P M H HI he q hq μ T Z hF ( fun i=> O (σ i) ) ( fun i=> U (σ i) ) ( Eventually.of_forall (fun i=> hc _) ) hx hR ha ( Eventually.of_forall (fun i=> hP _) ) hZ d p k|>.pay; let l:Filter ℕ:= atTop; obtain ⟨i,hi,hI⟩:= ( ( hV ).and ( ( ( tendsto_natCast_atTop_atTop ( R:=ℝ ) ).comp hσ.tendsto_atTop ).eventually ( eventually_ge_atTop c )) ).exists; apply not_lt_of_ge hi; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ( show c ≤ σ i from hI ) ( Fountain.cost_pos .. |>.le )) ( hL (σ i) ); -- field.apply
end point
end YM.FVA2.Elegant
