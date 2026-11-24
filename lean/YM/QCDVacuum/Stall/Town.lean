import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Class
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pallet
import YM.QCDVacuum.Stall.Friends
/-!
# Simultaneous held-U gauge readers for vector-label faces

Use real polar coordinates from Faction. No establishment of small-weight bounds from existential regularity! This file is integral coherence incl cof.V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m l : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation Packets Art Silica
variable {J : Type} [Fintype J] {τ:J ↪ Wing}

structure Township (τ:J ↪ Wing)(R:Rep G f)(T:Tube G S) where
  chorus : Config G c → Quartet J S R τ
  there (j:J) : Measurable (fun p:Config G c×Config G f=>((chorus p.1).has j).ingredient p.2)
  fixes (j:J)(k l:ℕ) : LocalOn (areas R T k l ((registry S τ) j)) (fun V=> ((chorus V).has j).ingredient)
namespace Township
variable (u:Township τ R T)(X:Coat T F)(p:Molecule S)

abbrev tune (V: Config G c):=u.chorus V
abbrev hire (V:Config G c):= (u.tune V).seat (tick τ p)
lemma chums (V:Config G c) : (u.hire p V).signs⊆p:=by rw [hire,Quartet.hei]; intro i hi; obtain ⟨j,h,rfl⟩:= mem_map.mp hi; exact (ticking ..).1 h
private abbrev tariffY (V:Config G c)(i:J)(a:ℝ)(w:Directions G f):= ((u.tune V).has i).paidU X a w
lemma quota_any (V:Config G c)(i:Finset J)(a:ℝ)(w:Directions G f): ((u.tune V).seat i).paidU X a w=∏ j∈i,u.tariffY X V j a w:=by unfold Faction.paidU Quartet.seat; dsimp only; rw [prod_map]; rfl
lemma tax_m {A:Type*} [MeasurableSpace A](Y:A→F.Slice G)(V:A→ Config G c)(w:A→ Directions G f)(h:Measurable Y)(hp:Measurable V)(hv:Measurable w): Measurable fun t=>(u.hire p (V t)).paidU (drive X (V t) (Y t)) a (w t):=by
   simp_rw [hire,quota_any]; refine Finset.measurable_fun_prod _ fun i _=>?_
   unfold tariffY Blade.paidU Blade.fond; simp_rw [Quartet.reserves]
   exact ((u.there i).comp (hp.prodMk (Art.entering X hp h hv))).mul ((X.enforce_b (2*a) (X.plaza (Matter.areas R T 0 X.B ((τ i).badge S)))).comp hv)
lemma chivalry (U V: Config G c)(hp:Agrees (ground R T l X.B p) U V)(x:Directions G f): (u.hire p U).paidU X a x=(u.hire p V).paidU X a x:= by
   simp_rw [hire,quota_any]; apply prod_congr rfl; intro j hj
   have hm :(u.tune U|>.has j|>.ingredient)= (u.tune V|>.has j|>.ingredient) := u.fixes j l X.B _ _ (agrees_mono hp (subset_biUnion_of_mem _ ((ticking τ p j).1 hj)))
   unfold tariffY Blade.paidU Blade.fond; simp_rw [Quartet.reserves]; rw [hm]
lemma ascot (U V: Config G c)(hp:Agrees (ground R T l X.B p) U V)(k:Finset ℕ)(z:Air f G): (u.hire p U).premium X W a Ñ k l z p=(u.hire p V).premium X W a Ñ k l z p:= by
   unfold Faction.premium; rw [if_pos (u.chums ..), if_pos (u.chums ..), u.chivalry X _ U V hp]; rw [show (u.hire p U).signs= _ from Quartet.hei .., show (u.hire p V).signs= _ from Quartet.hei ..]
lemma reckon (U V: Config G c)(hp:Agrees (ground R T l X.B p) U V)(k:Finset ℕ): (u.hire p U).tithe X k W a Ñ l p= (u.hire p V).tithe X k W a Ñ l p:= integral_congr_ae (ae_of_all _ fun z=> u.ascot (X.wrapY z.1) p U V hp k z.2) -- let
lemma coins (V:Config G c)(Y : Coat T F)(K:Support c){s q:Finset ℕ} {W:Air f G}(t:Air f G)(hp:Borough X Y K W t s q R)(hm:Room P S T X.x)(hh:500≤l)(hu:Intake P T X.x R)(hk: ground R T l X.B p⊆ K):
   (u.hire p V).paidU X a (worldZ X R.beta W)= (u.hire p V).paidU Y a (worldZ Y R.beta t):=by
   have h' := hp.rooms hm R.beta
   simp_rw [hire,quota_any]; refine prod_congr rfl fun i hi=>?_
   let M:=(u.tune V).has i
   have hv : areas R T l X.B (M.turn.badge S)⊆ K := (subset_biUnion_of_mem _ (show M.turn.badge S ∈ p from ((u.tune V).reserves i).symm ▸ ((ticking ..).1 hi))).trans hk
   have hZ : Footprint.enlargement S.ratio l X.B (RG.inspected M.crest)⊆ K:= by rw [M.turn.badge_area] at hv; exact hv
   have hh : ∀ i∈ areas R T 0 X.B (M.turn.badge S),Cleanroom K (30*X.B) i:=by
      intro i hi j hj; rw [M.turn.badge_area] at hi; obtain ⟨x,h,p⟩:= halo_spec.mp hi
      apply hZ; refine halo_spec.mpr ⟨x,h,(separation_triangle x i j).trans ?_⟩; rw [zero_mul] at p
      exact le_trans (add_le_add p hj) ((zero_add _).trans_le (Nat.mul_le_mul_right X.B (by omega)))
   change M.paidU _ _ _=M.paidU _ _ _
   have hx:= M.specific _ _ (h'.inherits hm (l:=l) (by omega) _ hZ)
   rw [X.oldysis hu.positive,Y.oldysis hu.positive] at hx
   have he := h'.enforces hm _ hh (2*a)
   rw [X.oldysis hu.positive,Y.oldysis hu.positive] at he
   unfold Blade.paidU Blade.fond; rw [hx,← hp.B,he]
end Township
end YM.PhysicalNext.Repeat.Lotus
