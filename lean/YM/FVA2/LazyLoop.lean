import YM.FVA2.MeshFilm
/-!
# uniform branch-loop bounds & `Pulled` differentiation
 -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real Metric
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High Wire Belt
open scoped BigOperators ContDiff Classical
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
local notation "Υ" => frameF I v
local notation "Δ"=> constantP G I (PlanetD G)
variable {x: Position W I}{U: Rake.Dance G I W}{a: W→Choice v S}
section estimates
variable (h:Mesh (frameF I v) x)(hu:Frozen a U x) {y z: Finset W}{A B:BH G}
-- uniform domination, no price constants depend on point index.Note
include h hu
lemma loopP [Nonempty I] (t:ℝ)(hp:y.Nonempty)(n:ℕ)(w:Legs ( Lane4 G )) : Sec (fun i q=> trc ( PlanetD G t ) q ( U y n i t ) w) planeF := by
    obtain ⟨T,f,F,g⟩:= pension h hu t; let P(i:I):T.time:= ⟨i,t,f i⟩; have hP:=g.1; obtain ⟨b,hb,hL,hG⟩:= g.2 y hp n; let K s (q:QP×ℝ):=trc ((plug ( J:=T.slot ) (constantP G I (PlanetD G))) s) q.1 ( plug (U y n) s ) ( sail ( ray w ) q.2 ); have hm:= topCycle (a:=1) hL F ( ray_course (fun i=> Bool.noConfusion i : Course false w) ) hb (fun i=>zero_le_one);
    have hz : (fun i q=> trc (PlanetD G t) q ( U y n i t ) w)= fun i q=>K (P i) (q,1):= by funext i q; unfold K; dsimp only; rw [ ray_sail ]; rfl;
    rw [hz]; apply DomR hP hm (fun i j=>?_); unfold positive; simp only [hG i j, (hP i j).2 ]; rfl
lemma packP [Nonempty I] (t:ℝ)(hp:y.Nonempty)(hx:z.Nonempty)(n k:ℕ)(w v:Legs (Lane4 G)) : Sec (fun i q=> meshZ (PlanetD G t) A B ( U y n i t ) ( U z k i t ) w v q) planeF := by
    obtain ⟨T,f,F,g⟩:= pension h hu t; let P(i:I):T.time:= ⟨i,t,f i⟩; have hP:=g.1; obtain ⟨b,hb,hL,hG⟩:= g.2 y hp n; obtain ⟨e,he,hX,hY⟩:=g.2 z hx k; have hh:= meshC (a:=1) F A B (add_split ( ray w ) ( ray v )) hL hX; let K:= packMesh A B ( plug ( J:=T.slot ) Δ ) (plug ( U y n )) (plug ( U z k )) ( ray w ) ( ray v ); -- type.Dup
    have hK : (fun i q=> meshZ (PlanetD G t) A B ( U y n i t ) ( U z k i t ) w v q)=fun i q=> K (P i) (q,1):=by funext i q; unfold K packMesh; simp_rw [ray_sail]; rfl
    rw [hK]; apply DomR hP hh (fun i j=> ?_); unfold Qbud positive; simp only [ Pi.mul_apply,Pi.one_apply,hG i j,hY i j,( hP i j ).2] -- args K let
lemma riverP {t:ℝ}(hp:2 ≤ y.card)(q:Legs (Lane4 G))(n:ℕ) : Sec (fun i s=> rhs x (fun _=>planeF) Δ Δ (approach Υ S) U y n i s q ) ( volume.restrict ( Iic t ) ):= DomT ( frontIn h hu hp n ) ( recall ( passage a h ) ( moneyCast a _ gulfG ) ( moneyCast a _ westV ) hu ( Finset.card_pos.mp ( by omega ) ) n ) q t
end estimates
section Sec
variable {V:Type}[MeasurableSpace V]{μ:Measure V}{F H:I→V→ℂ}
lemma Sec.sub (hF:Sec F μ)(hH:Sec H μ): Sec (F-H) μ:= by
    obtain ⟨x,r,hB,hr⟩:=hF; obtain ⟨y,q,hV,hq⟩:=hH; refine ⟨ fun i=> (x i).sub (y i), r+q,hB.add hV,?_⟩; filter_upwards [hr,hq] with u hr hq; intro v; exact ( norm_sub_le _ _ ).trans ( add_le_add (hr _) (hq _) )
lemma Sec.flux (c:ℂ)(hF:Sec F μ): Sec (c • F) μ:= by
    obtain ⟨x,r,hb,ht⟩:=hF; refine ⟨ fun i=> (x i).const_mul c,fun i=> ‖c‖* r i,hb.const_mul _,?_⟩; filter_upwards [ht] with i hi; intro j; exact le_trans (norm_mul .. |>.le) (mul_le_mul_of_nonneg_left (hi _) (norm_nonneg _)) -- syntax
lemma Sec.tempo {F:I→QP→ℂ}(g:I→QP→ℂ)(hv:∀ i,Continuous (g i)) (hp:∀ i q,‖g i q‖≤1)(hF:Sec F planeF): Sec (g*F) planeF:= by
    obtain ⟨x,r,h,hR⟩:= hF; refine ⟨ fun i=> Integrable.bdd_mul (x i) ((hv i).aestronglyMeasurable) ( Eventually.of_forall (hp i) ), r,h,?_ ⟩; filter_upwards [hR] with i hi; intro j; exact le_trans (norm_mul ..|>.le ) ((mul_le_of_le_one_left (norm_nonneg _) (hp j i)).trans (hi _))
lemma Sec.zero: Sec (0:I→V→ℂ) μ:= ⟨ fun _=>integrable_zero _ _ _,0,integrable_zero _ _ _,Eventually.of_forall (fun _ _=> by simp)⟩
end Sec
section motion
variable (d:QP)(k l:Finset W)(i:W) (p q:ℝ)
variable {Z:Set ℝ} (H:IsOpen Z)
-- two switches per set.W.g∈least. plus gradient row.`Sail B.Motion a pair.Geom.
def direct (Z: Set ℝ)(b c:ℂ)(f g:ℝ→ℂ): Prop := ∀ t∈Z,HasDerivAt f ( b*g t - c*f t ) t
def liftP (s: Finset W)(i:W):ℂ:= if i∈s then 1 else 0
def key (s: Finset W)(i:W): Prop:= ∃ h: s.Nonempty,s.min' h=i
def peak (s: Finset W)(d:QP)(i:W): QP:= if key s i then d else 0
lemma peak_single (h:W) : peak {i} d h=if i=h then d else 0:= by unfold peak; by_cases he:i=h <;> simp [key,he]
variable {b c:ℂ} {f f' g g':ℝ→ℂ} (Z)
section
variable (F H:Glade G ℝ)
abbrev Pulled (b c:ℂ)(w:Legs (Lane4 G)):= ∀u:ℝ,direct Z b c (fun i=>F i u w) (fun i=>H i u w)
def grade (Z: Set ℝ)(d:QP)(i:W)(l: Finset W)(F H:Glade G ℝ) := ∀ w:Legs ( Lane4 G ), Pulled Z F H ( liftP l i ) ( strike ( peak l d i ) ( net w ) ) w
end
variable {Z}
lemma direct.sumD (hf:direct Z b c f g)(hg:direct Z b c f' g'): direct Z b c (f+f') (g+g'):= by
    intro x hx; apply ( (hf x hx).add (hg x hx) : HasDerivAt (fun p=> f p+ f' p) _ _ ).congr_deriv; dsimp only [Pi.add_apply]; ring
lemma direct.scales (hf:direct Z b c f g)(t:ℂ): direct Z b c (t • f) (t • g):= by intro x hx; apply HasDerivAt.congr_deriv ( HasDerivAt.const_mul _ (hf x hx) ); simp only [ Pi.smul_apply, smul_eq_mul ]; ring
lemma direct.bulkD (p: Finset I)(u v:I→ℝ→ℂ)(h:∀ i∈p,direct Z b c (u i) (v i)): direct Z b c (∑ i∈p,u i) (∑ i∈p,v i):= by
    induction p using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty]; intro i hi; simp| insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (by simp)).sumD (ih (fun z hz=> h z (Finset.mem_insert_of_mem hz)))
variable {V:Type}[MeasurableSpace V]{μ:Measure V}{F' H':ℝ→V→ℂ}
include H
lemma direct.majorize (hF: Sec F' μ)(hH: Sec H' μ)(hr:∀ v,direct Z b c (fun x=> F' x v) (fun x=> H' x v)): direct Z b c (fun z:ℝ=>∫ x,F' z x∂μ) (fun z:ℝ=>∫ x,H' z x∂μ):= by
    intro i hi; let f:= b • H' - c • F'; obtain ⟨h,z,hz,he⟩:= Sec.sub (hH.flux b) (hF.flux c); apply HasDerivAt.congr_deriv ( ( hasDerivAt_integral_of_dominated_loc_of_deriv_le ( bound:=z ) ( H.mem_nhds hi ) ( Eventually.of_forall ( fun i=> (hF.1 i).aestronglyMeasurable ) ) (hF.1 _) (h i|>.aestronglyMeasurable) (he.mono fun y hy x _=> hy x) hz ( Eventually.of_forall ( fun i x hx=> hr _ _ hx ) ) ).2 ); simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; rw [ integral_sub ( (hH.1 i).const_mul b ) (( hF.1 i ).const_mul c), integral_const_mul,integral_const_mul ]
end motion
end YM.FVA2.Poesy
