import YM.Contacts.Procession.Cycle
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
/-! The polynomial-keeping canonical harmonic filter applies in every period of the analytic step. Can use truths on this representative via Slope & Health. No alterations to Rep.history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier
variable {G:Gauge}{n k i r l p j:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
-- all statements use the P from Actor, not stamping plot
open Place MultiNext.SignedSource Pattern Shuttle.Tide.Morning
lemma plateau (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E](n:ℕ)(h:0<n): Powers.space E4 E (n-1)= rangeLt E n:= by
    apply le_antisymm; · refine Submodule.span_le.mpr ?_; rintro f ⟨i,hi,hf⟩; exact exact_le_band (by omega: i<n) (can_write.mpr ⟨_,Powers.tensor_form hf⟩)
    intro f hf; obtain ⟨P,h,rfl⟩:=range_decompose hf; refine Submodule.sum_mem _ (fun u (hi:u∈Finset.univ)=>?_); obtain ⟨A,hx⟩:=can_write.mp (h u); rw [hx]; exact Powers.residence ⟨Tensor.diag_smooth ..,fun x v=> Tensor.homogeneous A v x⟩ (by have hx:=u.isLt; omega)
abbrev plate (G:Gauge):Type:= E4→Axis→G.Color
def sheen (F: Window G.Color)(x:Node (Dye G)):ℝ:= F x.1 (axisEquiv.symm x.2.1) x.2.2
variable {L : Side}
def seen (R:Spine.voyage L)(F:Window G.Color)(x y:Node (Dye G)):= install (Origin.bleed G R) x y*sheen F y -- variable L
private def chute {w: G.ColorIndex} (L:Side)(x: Cover) : Axis × Cover ↪ Node (Dye G):= ⟨fun p=> (cellar L x+p.2, coord p.1,w),fun i j h=> Prod.ext (axisEquiv.injective (congr_arg (fun q=>q.2.1) h)) (add_left_cancel (congr_arg Prod.fst h))⟩
variable {R:Spine.voyage L}{F:Window G.Color}
lemma street (L: Side)(x:Cover): rent L x=cellar L x:= (rent_unique (Carrier.balance L x)).symm
lemma fetch (R:Spine.voyage L)(F:Window G.Color)(x:Cover)(a: Axis)(w:G.ColorIndex)(y:Axis)(z:Cover) : seen R F (x,coord a,w) (chute (w:=w) L x (y,z))= (member R x a y z • F (cellar L x + z) y) w:= by
    unfold seen sheen install member; change Origin.bleed G R _ (coord y,w) ((cellar L x+z)-rent L x)*F _ (axisEquiv.symm (coord y)) w= _; rw [street, add_sub_cancel_left,show axisEquiv.symm (coord y)=y from axisEquiv.symm_apply_apply y]; unfold Origin.bleed; rw [if_pos rfl]; rfl
-- itinerary at each stamped x, also useful for cereal. exact physical orientation
lemma ember (h:Whole R)(hf:Carries F k b)(x:Node (Dye G)): HasSum (seen R F x) (sheen (applyLine R F) x):= by
   obtain ⟨s,C,hs,hc⟩:= h; rcases x with ⟨x,a,w⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a; let u:= chute (w:=w) L x; let X (v:Axis)(z:Cover):= member R x a v z • F (cellar L x+z) v
   let A(v:Axis):= stream (member R x a v) (cellar L x) (fun z=> F z v); have hx(y:Node (Dye G))(hv:y∉ Set.range u) : seen R F (x,coord a,w) y=0:= by
      have he:y.2.2 ≠ w:=by rintro h; apply hv; obtain ⟨j,hj⟩:=axisEquiv.surjective y.2.1; refine ⟨(j,y.1 - cellar L x),Prod.ext (by change _+(_-_)=_; abel) (Prod.ext hj h.symm)⟩
      unfold seen install Origin.bleed; change (if w=y.2.2 then _ else (0:ℝ)) * _=_; rw [if_neg (Ne.symm he),zero_mul]
   let V:= EuclideanSpace.proj (𝕜:=ℝ) w; let q:=(x,coord a,w); have ha (v): HasSum (X v) (A v):= (stream_income hs (hc (wrap L x,coord a) (coord v)) (cellar L x) k hf.1 (fun z=> hf.2 z v)).2.1.of_norm.hasSum
   have hQ v: HasSum (fun z=>seen R F q (u (v,z))) (V (A v)):= by rw [show (fun z=> seen R F q (u (v,z)))= _ from (show _= V ∘ X v from funext (fetch R F x a w v))]; exact V.hasSum (ha v)
   apply (u.injective.hasSum_iff hx).1; let p (p:Axis×Cover):=seen R F q (u p); have hP: Summable p:=Summable.of_norm ((summable_prod_of_nonneg (f:=fun p':Axis×Cover=>‖p p'‖) (fun p' => norm_nonneg _)).2 ⟨fun v=> (hQ v).summable.norm,Summable.of_finite⟩)
   have hs : HasSum p (∑ v:Axis,V (A v)):= by rw [show (∑ v:Axis,V (A v))=tsum p from ?_]; exact hP.hasSum; rw [hP.tsum_prod,tsum_fintype]; exact Finset.sum_congr rfl (fun v _ => (hQ v).tsum_eq.symm)
   convert hs using 1; · rfl
   unfold sheen; dsimp only [coord_map]; rw [show axisEquiv.symm (coord a)=a from axisEquiv.symm_apply_apply a]; -- fails coord_map
   unfold applyLine; exact map_sum V A Finset.univ
-- Scent_R column polynomial.F.W.Account for offsets later
abbrev sense (f: plate G): Node (Dye G)→ℝ:= sheen (verdict (E:=G.Color) f)
lemma clue (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E](n:ℕ)(b:ℕ)(h:n≤b)(hx:0<n) : rangeLt E n≤ Powers.space E4 E (b-1):= by rw [plateau _ _ (by omega)]; exact grows E h
lemma particle (f:plate G) (h: f∈ Place.rangeLt (Axis→G.Color) n)(H:0<n) (a:Axis) : (fun z=>f z a)∈ Powers.space E4 G.Color (n-1):= by rw [plateau _ n H]; exact linear_band (ContinuousLinearMap.proj a) n h
lemma quarter (V : Node (Dye G)→ℝ)(h:0<n) : (∃ f∈ Place.rangeLt (Axis→G.Color) n, V=sense (G:=G) f) ↔ ∃ f: Axis→ E4 → G.Color,(∀ a,f a∈ Powers.space E4 G.Color (n-1)) ∧∀ z a i,V (z,coord a,i)= f a (xyz z) i := by
   constructor; · rintro ⟨f,hf,rfl⟩; refine ⟨fun a z=> f z a, fun a=> particle f hf h a, fun z a i=>?_⟩; unfold sense sheen; dsimp only; rw [show axisEquiv.symm (coord a)=a from axisEquiv.symm_apply_apply a]; rfl
   rintro ⟨f,hf,H⟩; refine ⟨(fun z a=>f a z),vector_band f (?_),?_⟩; · intro i; exact plateau G.Color n h ▸ hf i
   funext x; rcases x with ⟨z,a,i⟩; obtain ⟨p,rfl⟩:=axisEquiv.surjective a; unfold sense sheen; dsimp only; rw [axisEquiv.symm_apply_apply]; exact H z p i
/-- Uncontracted harmonic transmission through all levels of finite temperature and horizon gates.
Engineering reproduction, no lift to Snap at zero.Budget powers earlier. -/
theorem stepping (Q: Flight j i) (hi:4 ≤ i)(hb:0<b)(hn:n ≤ j) (f:plate G)(h:f∈ Place.rangeLt (Axis→G.Color) n): ∃ v∈ Place.rangeLt (Axis→G.Color) n, v-unitStep Q.L^n • f∈Place.rangeLt (Axis→G.Color) (n-1) ∧ ∀ x:Node (Dye G), HasSum (seen (linesOf Q b) (verdict (E:=G.Color) f) x) (sense (G:=G) v x):= by
   obtain ⟨q,hq,ht,H⟩:= accepts_V b hb Q hi hn f h; refine ⟨q,hq,ht,fun x=>?_⟩; obtain ⟨M,hM⟩:= royalties n f h; unfold sense; rw [← H]; exact ember (stored Q b hb hi) hM x
end YM.Contacts.Procession.Pierian
