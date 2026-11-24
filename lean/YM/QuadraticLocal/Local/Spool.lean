import YM.QuadraticLocal.Local.Story
import YM.Next.MULTISOURCE.Recenter
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Venue
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open RemainderComparison RemainderComparison.Portal RemainderComparison.WickReps
open AllOrder AllOrder.Catch AllOrder.Wheel AllOrder.Wheel.Ride Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G:Gauge) (L:Side) (V:RG.Stage) (w:ℝ→ℕ)
namespace Spool
variable {G L w V} {η t x a b:ℝ} (h:Spine G L V w η t)
variable {c f:Side} {j r κ m:ℕ} (hj:2*j≤ f.val)(hm:2*w t< c.val)(hq:j+1≤w t)
variable {H F: Config G f→ℝ}{P:BudgetPoint}(hT:P.threshold=temp t) (hp:P.threshold≤2*Pressure.fiery G t L) (ht:P.order=V.order)
variable {S:Type}{u:S→ Config G f→ℝ} (hS:Tally P S u b)(hb:0≤ b)(ha:0≤ a)(hF:P.Regular univ H)
    (he:∀ V∈Boulevard.sunny P,F V=H V+ unite u V)
    (hX:∀ W:Positions (Uniform.Primary f G),‖W‖≤ Pair.velocity G L η t→ flags P.threshold (Boulevard.actual W)=∅ → Brush V.order a (Pair.velocity G L η t)⁻¹ (F ∘ Boulevard.actual) W)
local notation "Z"=> w t
set_option quotPrecheck false
local notation "b₀"=>Boulevard.ticket V.order a + b
-- recenter f-equivalence reserved estimate after projection. Port House.Y.Authority. Match at ANY congruence even CRT not canonical `home` when base plates very large. Does not translate the actual ROOT spec! adapt RGComparison01/Marks/Rotunda helpers.
variable (x:Site f) (A:Config G f)
open Multi.AxisShift
def south (u: Positions (Uniform.Primary f G)) (i:Uniform.Primary f G):ℝ:= u ((i.1.1+x,i.1.2),i.2)
lemma yank (u:Positions (Uniform.Primary f G)): translate x (Boulevard.actual u)=Boulevard.actual (Spool.south x u):=by
 funext p; change represent _ _= represent _ _; simp_rw [Work.F03.represent_link]; rfl
lemma ocean (u:Positions (Uniform.Primary f G)): ‖south x u‖≤‖u‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm u ((i.1.1+x,i.1.2),i.2)
include hF
lemma translationP : P.Regular univ (H ∘ translate x):=by
  have hX : ∀ U:Config G f, Healthy P.threshold univ U→ Healthy P.threshold univ (translate x U):= fun U h=> (health x univ ..).2 (h.mono_left (Finset.subset_univ _))
  have hx (U) (hU: Healthy P.threshold Finset.univ U): Push.Local.Chart P.order (H ∘ translate x) U:=by
    let z:Directions G f→L[ℝ] Directions G f:= Multi.AxisShift.evolve x
    have he':=hF.smooth _ (hX U hU); exact (show ContDiffAt ℝ (↑(↑P.order:ℕ∞):WithTop ℕ∞) (fun v=> H (increment (translate x U) v)) (z 0) from (map_zero z).symm ▸ he').comp _ z.contDiff.contDiffAt -- fix x
  refine ⟨fun i j h=> ?_,hF.borel.comp (Multi.AxisShift.visible x).measurable,fun q U=>?_,hx,fun U hu A l hl=>Next.Foundations.left_has _ hl (hx U hu)⟩
  · have ht:i=j:=funext fun k=> h k (mem_univ _) (mem_univ _); rw [ht]
  change H (translate x (gauge q U)) = _; rw [show translate x (gauge q U)=gauge (fun y=> q (y+x)) (translate x U) from ?_,hF.symmetry]; rfl
  funext e; simp only [Lattice.gauge,Lattice.translate]; rw [add_right_comm e.1 x (step e.2)]
omit hF
lemma shifts (H:Config G f→ℝ)(l:List (Directions G f)) (U:Config G f) : leftDerivs (H ∘ translate x) l U= leftDerivs H (l.map (Multi.AxisShift.evolve x)) (translate x U):= by induction l generalizing U with | nil=>rfl | cons v k ih=> simp only [List.map_cons,leftDerivs,ih]; rfl
local notation "H'" x:max=> (H ∘ translate x)
include h hm hq hT hp ht hS he hb ha hF hX
lemma territory (o: Site c): P.Regular (neighbors (w t) o) ((H ∘ translate x) ∘ Slide.shape (cognac hj) o) ∧ P.supBounds o (neighbors (w t) o) ((H ∘ translate x)∘Slide.shape (cognac hj) o) (Trio.tilt P (w t)* (Boulevard.ticket V.order a+b)):= by
   let H₀:=H ∘ translate x; let v:=H₀ ∘ Slide.shape (cognac hj) o; let hE:=translationP hF x -- order? x after hF
   let s:=neighbors (w t) o; let b':= Boulevard.ticket V.order a+b; have hh : P.Regular s v:= Arc.regular o hq hE; refine ⟨hh, mul_nonneg (by unfold Trio.tilt; positivity) (by unfold Boulevard.ticket; positivity), fun U hu l hl hd=>?_⟩
   obtain ⟨a,Y,hY,hW⟩:= h.fit P hp c f hm j hq hj o U hu; let X:= Lattice.gauge a (Slide.shape (cognac hj) o U)
   have hz i:= Slide.village hj o i; have hv : flags P.threshold (Slide.shape (cognac hj) o U)=∅:= Slide.allFlag (cognac hj) o U s (fun i=> (neighbors_mem ..).2 ((hz i).trans (Nat.le_of_lt hq))) P.threshold P.threshold_pos.le hu
   have hF₀: flags P.threshold X=∅:= by unfold X; rw [gauge_flags,hv]
   have hy: flags P.threshold (Boulevard.actual (south x Y))=∅:=by rw [← yank,hY,← pull_one]; exact Pane.tranquility _ hF₀ ..
   have h': 0<furl G L t:= Real.rpow_pos_of_pos h.price _; have hw := h.default P hT hp ht f (south x Y) ((add_le_add (ocean x Y) le_rfl).trans_lt hW) hy S u H F _ _ hS hF he (fun W' hW hV=> hX W' ((le_add_of_nonneg_right (show 0≤2*furl G L t from by positivity)).trans hW.le) (smoky hV)); rw [← yank,hY] at hw
   refine Arc.vetted o (cognac hj) U a (fun i=> (hz i).trans (Nat.le_of_lt hq)) (hE.smooth _ (by unfold Healthy; rw [hv]; simp)) (hh.smooth _ hu) hE.symmetry (hE.smooth X (by unfold Healthy; rw [hF₀]; simp)) ?_ l hl hd
   intro l hl hp; change ‖leftDerivs (H ∘ translate x) l X‖ ≤ _; rw [Spool.shifts x]; apply hw _ (by simpa using hl); intro i hi; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi; exact (pi_norm_le_iff_of_nonneg P.threshold_pos.le).2 fun i=> (norm_le_pi_norm j _).trans (hp j hj)
variable (hr:2*r≤ j) (hg:2*w t≤ m)(o:Site c)(g:Config G c→ℝ)
-- use translation at home.Carriers etc.
omit h hm hq hT hp ht hS he hb ha hF hX
def shift (x:Site f)(r:ℕ):= home f r-x
abbrev sewn (H:Config G f→ℝ)(r:ℕ): Config G c→ℝ:= (H ∘ translate (shift x r))∘ WickReps.garment hj o r
local notation "X₀"=> sewn hj x o
structure Lending (H:Config G f→ℝ)(P:BudgetPoint)(r:ℕ) : Prop where
 look : LocalOn (neighbors r o) g
 price (U:Config G c)(W:Config G f)(hu:flags P.threshold U=∅)(hx:flags P.threshold W=∅) (he:Agrees (Lattice.box r) (expandAt o U) (expandAt x W)): g U=H W
-- Annotation at arbitrary η_P.Tile. Phase motion, not pretending label identity
variable (hM:Lending x o g H P r)
include h hm hq hT hp ht hS he hb ha hF hX hr hg hM
lemma ahead (hn:4*r+16≤c.val): let f:=sewn hj x o H r; let b:=burse P m (w t) (Boulevard.ticket V.order a+b)
               P.Regular (neighbors m o) f ∧ (∀ U:Config G c,Healthy P.threshold (neighbors m o) U → g U=f U) ∧ ∀ x∈neighbors m o, P.supBounds x (neighbors m o) f b:= by
 let V₁:= translate (K:=G.El) (shift x r); intro f' b; let g₀:= H ∘ V₁; have hh:= territory h hj hm hq hT hp ht hS hb ha hF he hX (shift x r) (ploy o r); refine ⟨CouplingShape.reg_extend hh.1 (reaches hr o hq hg), fun U hV=> ?_,fun x hx=> sup_larger (postage (ploy o r) f' hh.1 hh.2 x ?_) (reaches hr o hq hg)⟩
 · have hp: RemainderComparison.WickReps.Matches g g₀ P r o 1 := by
       refine ⟨hM.look,fun U B hU hb hs=>?_⟩; rw [one_mul]; apply hM.price U (V₁ B) hU; · unfold V₁; rw [← pull_one]; exact Pane.tranquility _ hb ..
       have hx:expandAt x (V₁ B)=expandAt (home _ r) B:= by funext e; change B (wrap _ e.1+x+shift x r,e.2)=B (_,e.2); rw [add_assoc _ x,shift,show x+(home _ r-x)=home _ r by abel]
       rw [hx]; exact hs
   exact (refined g₀ hj hr o hq hg U hn hp hV).trans (one_mul _)
 apply le_trans (separation_triangle _ o x); rw [separation_comm]; have hf:=meters (r:=r) o; have hQ : separation o x≤ m:= (neighbors_mem ..).1 hx; omega
end Spool
end YM.QuadraticLocal.Venue
