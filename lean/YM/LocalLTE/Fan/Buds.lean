import YM.LocalLTE.Fan.Earn
/-! tag-independent core margin. Θ.* marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
lemma tighten (u:F.Slice G)(p:Disk G c)(b:Directions G f):let Z:= X.wrapY u
   (timeΛ Z p).input b=(timeΛ X p).input b ∧ (∀ s i,strain (timeΛ Z p) s i b=strain (timeΛ X p) s i b)∧ voltage (timeΛ Z p)=voltage (timeΛ X p):=by
 intro Z; let V:= timeΛ X p; let V':= timeΛ Z p
 have H b s i: strain V' s i b=strain V s i b:=by unfold strain; rw [show (timeΛ X p).signal b=X.blank.lens b from signal_for .., show V'.signal b=X.blank.lens b from signal_for ..]; rfl
 refine ⟨(chosen Z (Vine.pass p) b).trans (chosen X (Vine.pass p) b).symm,H b,?_⟩
 have he : Vine.bar V' 0= Vine.bar V 0 := by funext i; unfold Vine.bar; rw [H]; rfl
 unfold voltage well leanB; rw [he]; rfl
lemma wrapV (u:F.Slice G)(p:Disk G c)(b: Air f G)(i:Veil c f): vows (X.wrapY u) R Q a p b i= vows X R Q a p b i:= by
  let Z':=X.wrapY u; let Z:=timeΛ X p; let D:=timeΛ Z' p
  let q:=worldZ Z R.beta b; have hk:voltage D=voltage Z:=(tighten X u p (0
    )).2.2; have hz:worldZ D R.beta b=q:= by unfold q worldZ; rw [hk]; rfl
  have ht (q:Directions G f) (s:Signed)(i:Spot c f):Vine.costs D q s i = Vine.costs Z q s i:=by
     unfold Vine.costs; refine sum_congr rfl fun j _=> ?_; change (if D.selected _ _ then ‖strain _ _ _ _‖^2 / 2 else 0)=_; unfold Vine.pot; rw [(tighten X u p q).2.1 s j]; rfl -- edit
  unfold vows; change Polar.logMoment D a R Q.table (worldZ D R.beta b) (D.input (worldZ D R.beta b)) _ _=_; rw [hz, (tighten X u p q).1]
  change Polar.logMoment D a R Q.table q (Z.input q) _ _ = Polar.logMoment Z a R Q.table q (Z.input q) _ _
  have hp (j:LogLetter c f)(t:Directions G f)(U:Config G f): Polar.logMoment D a R Q.table t U b (.inl j)=Polar.logMoment Z a R Q.table t U b (.inl j) := by
    change Polar.frost .. = Polar.frost ..; rfl
  rcases i with i|i|i|i|i
  · exact hp (.inl i) q _
  · exact hp (.inr (.inl i)) q _
  · exact hp (.inr (.inr (.inl i))) q _
  · exact hp (.inr (.inr (.inr (.inl i)))) q _
  rcases i with i|i|i
  · change Polar.hover D a R q _ _= Polar.hover Z a R q _ _; unfold Polar.hover Polar.rootface; rw [hk,ht,ht]; rfl
  · change D.undercurrent i=Z.undercurrent i; rfl
  change D.solo q _ _ _= Z.solo q _ _ _; rfl

def pool (I: Finset (Tubular f G))(X: Coat T F)(p:Disk G c):= Poll.sweep (Pond.circuit I (timeΛ X p).relating)
instance (I: Finset (Tubular f G))(X: Coat T F)(p:Disk G c): IsProbabilityMeasure (Fan.pool I X p):= by unfold Fan.pool; infer_instance
def arm (I:Finset (Veil c f)): Molecule S:= I.image (elastic (S:=S))
def node (X:Coat T F)(p:Disk G c)(R:Rep G f)(Q: YM.ConnectedActivityE6.Target G P)(a:ℝ)(u : Finset (Veil c f))(b:Air f G):=
   ∏ i∈ u, (Real.exp (vows X R Q a p b i)-1)
lemma spool (p:Disk G c)(u:Finset (Veil c f))(I:Finset (Tubular f G))(h: (Pond.circuit I (timeΛ X p).relating).PosDef)(K : ℝ): bars I (timeΛ X p) (arm u) R Q.table K a n=∫ b,node X p R Q a u (Pond.spill I b) ∂ Fan.pool I X p:=by
  let Z:= timeΛ X p
  have he (x:F.Slice G)(b:Air f G): Polar.floating (Z.wrapY x) a R K Q.table b (own (arm (S:=S) u)) n (arm u)= node X p R Q a u b := by
    unfold node Polar.floating; rw [arm,prod_image]; swap; · exact fun i _ j _ h=> runOut h
    refine prod_congr rfl fun i _=> congr_arg (fun x=>Real.exp x-1) (wrapV X x p b i)
  unfold bars Fan.pool; change (∫ x:F.Slice G, (∫ b,lens₀ (circuit I Z.relating) b*Polar.floating (Z.wrapY x) a R K Q.table (Pond.spill I b) (own (arm (S:=S) u)) n (arm u)) ∂F.order G)= _ ; simp_rw [he]; rw [integral_const,probReal_univ,one_smul]; exact (Shield.recommends _ h _).symm
end YM.LocalLTE.Fan
