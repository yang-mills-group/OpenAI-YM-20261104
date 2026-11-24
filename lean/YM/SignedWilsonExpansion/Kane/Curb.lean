import YM.SignedWilsonExpansion.Belfry.Clerk
import YM.PhysMS.Frame.Phases
import YM.AllOrder.Leading.Solve
/-!
# Spin footpath for the official Election. Work with any Leading W; use Root.inc
 with stored tuition loans. Scope assembled from Waist ceremony & Book threshold
 AFTER stake.Exposes W & t for $r,r'$ before Ξ.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Kane
open Function Filter Set Table Spec Climb Trace Trace.Pilot PhysMS PhysMS.Frame
open Extraction Order Spin Next.UVStress OPE OPE.Orbits Levy
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 Dframe FVA2.Scale.Level Future
open Belfry Belle Dancer Belfry.Crisis Belfry.Classroom Belfry.ScaleFits Commission
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(W:ℝ→tower S)(L:Leading F W)
variable {b d e j n:ℕ}{ι:Type}{l:Filter ι}{g r ε:ι→ℝ}
namespace Tilted
abbrev walk (W:ℝ→tower S)(r:ℝ)(d:ℕ) : Sec G d ≃ₗ[ℂ] S.Field d :=( fields C.labels d ).symm.trans ( W r d )
abbrev bend (i j:ℝ)(d:ℕ) : FieldEnd G d:=( ( walk W j d ).trans ( walk W i d ).symm ).toLinearMap
lemma swing (r t:ℝ)(x:Sec G d): walk W r d ( bend W r t d x )= walk W t d x :=LinearEquiv.apply_symm_apply ..
lemma bend_r (r t z:ℝ)(d:ℕ): bend W r t d * bend W t z d=bend W r z d:=by ext1 x; apply ( walk W r d ).injective; rw [Module.End.mul_apply, swing, swing,swing]
@[simp] lemma bend0 (r:ℝ)(d:ℕ): bend W r r d= 1:=LinearMap.ext fun x=> LinearEquiv.symm_apply_apply ( walk W r d ) x
abbrev sPlot (p:Viewers F)(r:ℝ)(d:Caps n)(W:∀ i:Fin n,Sec G (d i) →ₗ[ℂ] S.Field (d i))(x:Points n): MultilinearMap ℂ (fun j=> Sec G (d j)) ℂ := ( S.classMoment ( spectator F p ) d (r•x) ).compLinearMap W -- t unused remove
abbrev PlotW (p:Viewers F)(r:ℝ)(d n:ℕ)(x:Points n): Point G d n:= sPlot F p r (fun _=>d) (fun _=> ( walk W r d ).toLinearMap) x
variable {F W}
abbrev current (C:Family G)(d:ℕ):= Maxwell.Free.fields C.labels d
abbrev Seats (W:ℝ→tower S)(g:ι→ℝ)(p:ι→Viewers F): Gallery G ι:= fun i d n=> PlotW F W (p i) (g i) d n
lemma reflectW (i:Viewers F) (r:ℝ)(x:Points n)(u:Tags G d n) : PlotW F W i r d n x u=measured F i (W r) (d:=fun _=> d) (fun j=> ( fields C.labels d ).symm (u j)) r x:=rfl
omit L
lemma Plot_neat (v: Viewers F) {ρ:ℝ}(h:0<ρ) (x:Tags G d n): ContDiffOn ℝ ∞ (fun u=> PlotW F W v ρ d n u x) (conf n):=by
    let y(i):= walk W ρ d ( x i ); let t(i): S.Tag:= ⟨d,y i⟩; exact ( S.class_smooth _ (spectate F v).smooth t ).comp ( contDiffOn_id.const_smul ρ ) ( fun u H=> Work.A05.smul_conf h H ) -- name
lemma zero (d n:ℕ)( x:Points n)(u:Tags G d n) : WickGoal (C:=C) (d:=fun _=>d) (fun i=> (fields C.labels d).symm (u i)) x= scene x d u:=by -- infer
  let t(i : Fin n) : (Bel C.book).Tag := ⟨d,(Maxwell.Free.fields C.labels d).symm (u i)⟩
  change (Bel C.book).useAt (Bel C.book) x t = scene x d u
  rw [Maxwell.Free.display]; have he : Maxwell.Free.supply C.labels ∘ t = fun i => (u i).val := by
    funext i;change Maxwell.Free.address C.labels d ((Maxwell.Free.fields C.labels d).symm (u i))=_
    rw [Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply]
  rw [he]; rfl
include L
lemma viaPlot (v:ι→ Points n)(x:Points n)(hx:x∈conf n)(r₀:Tendsto r l trail)(p:Tendsto v l (𝓝 x))(u:Tags G d n) : Tendsto (fun i=> PlotW F W none ( r i ) d n (v i) u ) l (𝓝 (scene x d u)) :=by rw [← zero (C:=C)]; exact leading_at F L _ r₀ p hx
lemma risePlot (h:d≤b)(r₀:Tendsto r l trail): ∀ᶠ i in l,∀ x:Sec G d, walk W ( r i ) b ( Normalize.up h x )= F.sector.derivatives.rise h ( walk W ( r i ) d x ):=by
    filter_upwards [ r₀.eventually ( L.raised h ) ] with i hi x; refine Eq.trans (congrArg (W (r i) b) (?_)) ( hi ( (current C d).symm x )); apply address_inj C.labels b; rw [address_eval,current,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply, address_rise,address_eval, LinearEquiv.apply_symm_apply]; rfl -- defeq ν
lemma riseView (v: ι→Viewers F)(h:d≤b)(r₀:Tendsto r l trail) (n:ℕ): ∀ᶠ i in l,∀ u:Tags G d n,EqOn (fun x=>PlotW F W (v i) (r i) d n x u) (fun x=>PlotW F W (v i) (r i) b n x (Normalize.up h ∘ u)) (conf n):=by
    filter_upwards [risePlot L h r₀,r₀.eventually ( show ∀ᶠ x in trail,0 < x from self_mem_nhdsWithin )] with i hi hv u x hx; change S.classMoment ( spectator F (v i) ) _ _ _= S.classMoment ( spectator F (v i) ) (fun _:Fin n=>b) (r i•x) ( fun j=> walk W (r i) b ( Normalize.up h ( u j ) ) ); simp_rw [ hi ]; exact (AllOrder.Leading.moment_inclusion (spectate F (v i)).laws.toSymmetric (spectate_ready F (v i)) (fun (_:Fin n)=> h) (Work.A05.smul_conf hv hx) (fun j=> walk W (r i) d ( u j )) ).symm
lemma SpinW (r₀:Tendsto r l trail)(d:ℕ): ∀ᶠ i in l, walk W ( r i ) d ( Normalize.leaf G d )= S.unit d ∧ (∀ x:Sec G d, walk W (r i) d ( reel d x )= S.conj F.room.kernel.spin d (walk W (r i) d x)) ∧ ∀ (s:Signed)(x:Sec G d),walk W (r i) d ( ori s.ortho d x )=S.mirror F.room.kernel.spin d s (walk W ( r i ) d x):=by
    let B:=fields C.labels d; let A:= (Bel C.book); let q:=Maxwell.Free.spin_free C.labels; filter_upwards [r₀.eventually ( L.equivariant d ),r₀.eventually ( L.unit d )] with i hp hv; have he(x): Free.address C.labels d ( B.symm x )= x.val:= by rw [Free.address_eval]; exact congr_arg Subtype.val (B.apply_symm_apply _)
    refine ⟨ (congrArg ( W (r i) d ) (show B.symm (Normalize.leaf G d)=A.unit d from address_inj C.labels d (by rw [ he, Maxwell.Free.unit_address ]; rfl))).trans hv ,fun x=> (congrArg (W (r i) d) (show B.symm (reel d x)=A.conj q d (B.symm x) from ?_)).trans (hp.2 _),fun s x=> (congrArg (W (r i) d) (show B.symm (ori s.ortho d x)=A.mirror q d s ( B.symm x ) from ?_)).trans (hp.1 s _) ⟩
    · apply address_inj C.labels d; rw [he, address_star,he]; rfl
    apply address_inj C.labels d; rw [he,address_motion,he]; rfl
-- real path.L
lemma adm_bend (r₀:Tendsto r l trail)(h:Tendsto g l trail)(d:ℕ) : ∀ᶠ i in l,adm ( bend W (r i) (g i) d ):=by
   let B(i):=bend W (r i) (g i); let X(i):=walk W (r i); let V(i):=walk W ( g i ); have he(t:Fin (d+1)) : ∀ᶠ i in l,∀ x:Sec G t,B i d (Normalize.up (Nat.le_of_lt_succ t.isLt) x) = Normalize.up (Nat.le_of_lt_succ t.isLt) ( B i t x ):=by
      let k:= Nat.le_of_lt_succ t.isLt; filter_upwards [risePlot L k r₀,risePlot L k h] with i hi ht v; apply ( walk W (r i) d ).injective; rw [hi]; unfold B; rw [swing,swing,ht]
   filter_upwards [eventually_all.mpr he,SpinW L r₀ d,SpinW L h d] with i hi ⟨h₁,h₂,h₃⟩ ⟨v₁,v₂,v₃⟩; refine ad_sub _ (?_); rw [ may_change ]; simp only[LinearMap.sub_apply,Module.End.one_apply]; refine ⟨sub_eq_zero.mpr ( (walk W (r i) d).injective ((swing ..).trans (v₁.trans h₁.symm)) ), fun y p x u=> ?_,fun p=>?_,fun s p=>?_ ⟩
   · let u': Sec G y:= ⟨ _, u ⟩; refine Submodule.sub_mem _ ( ?_ ) u; exact (show (B i d x).val ∈ shellSector G y from (congr_arg Subtype.val (hi ⟨y,Nat.lt_succ_of_le p⟩ u')) ▸ (B i y u').property )
   · rw [map_sub, show (bend W (r i) (g i) d) (reel d p)=reel d ((bend W (r i) (g i) d) p) from ( walk W (r i) d ).injective (by rw [swing,v₂,h₂,swing]) ]
   rw [map_sub, show (bend W (r i) (g i) d) (ori s.ortho d p)=ori s.ortho d ((bend W (r i) (g i) d) p) from ( walk W (r i) d ).injective (by rw [swing,v₃,h₃,swing]) ]
end Tilted
end YM.SignedWilsonExpansion.Kane
