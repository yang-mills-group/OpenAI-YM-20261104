import YM.FVA2.Position.Frugal
/-!
# Projecting to the actual unit (D and Native)

Use the `comet` with these data. See also `Position/Hall.lean`, which selects a
unit-compatible representative of the MS parameters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Ace
open Function Set Filter Finset MeasureTheory
open MS MS.Momentum MS.Arts MS.Koszul MS.Plane MS.Theater MS.Garment MS.Wind
open MS.Pearl MS.Rock MS.Alps MS.Halo MS.Mach MS.Motif
open MS.Hem MS.Hem.Mell MS.Dock MS.Train _root_.YM.MS.Shine MS.High MS.High.Knobs
open MS.Outlook MS.Color MS.Native MS.Native.Wilsonian MS.Landau MS.Landau.Detect
open MS.Book MS.Book.Program MS.Book.Convolve MS.Heat MS.Local.Physical MS.Land
open Garment.Wave Garment.Wick MS.Emit -- disamb
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n:ℕ}{G:Gauge}
-- engineering programme. unit is weighted vector not requiring `finBasis` to be normalized.
abbrev pawnMob (G:Gauge)(t:ℝ) : Mob G:= fun _=> coin (t:ℂ)
lemma ccash (a f:ℂ){I:Type}: (coin (A:=I) (f*a))=f • coin a:= by ext l; cases l <;> first | rfl | exact (mul_zero f).symm
abbrev Brace (G:Gauge)(t:ℝ): Coat G:= fun _=> pawnMob G t
abbrev baseFlat (G:Gauge)(t:ℝ): Flats G:= Finsupp.single 0 (Brace G t)
abbrev UnitF {X:Type}[Zero X](v:X): T X:= fun i=>if i=0 then v else 0
local notation "x₀"=> baseFlat G
lemma lease (t:ℝ): Pace (pawnMob G t m) 0 0 0:= by
 rw [pawnMob, show coin (↑t:ℂ)= (↑t:ℂ) • coin (A:=Shore G m) 1 from ( by rw [← ccash,mul_one]) ]; exact Pace.unit.cash (by simp)
lemma badge (t:ℝ): Count (Brace G t) 0∧Cap0 false 0 0 (Brace G t):= by
   have he : Sturdy false (pawnMob G t):= ⟨fun i X _=> vaultLeaf _ _, fun p l=>by cases l <;> rfl⟩
   have hv : ShadeG (pawnMob G t):= fun n u=> Mach.Safe.cpig _ u
   have hs :∀ i,Pace ( pawnMob G t i ) 0 0 0:=fun _=> lease t
   have ht:= Pace.priceV hs; refine ⟨fun _=> Pace.homer hs,⟨⟨?_,?_⟩,?_,?_⟩,?_ ⟩; exacts [ mer.uLive ( Live.stays ht ),Eventually.of_forall fun _=>he, Eventually.of_forall fun _=> (show Collar 0 _ from ⟨ fun n=> (hs n).sym,hv,fun n=>(hs n).ghost ⟩), (show realAlong _ _ from Eventually.of_forall fun _ x=>(hs x).sense), Eventually.of_forall fun _ x=>(hs x).up ]
lemma tree_p {Q:Type}[Fintype Q]{I:Type}[AddCommGroup I]{r:Sector Q}(F: Row Q I ℂ)(K: Plane.Flux Q I ℂ)(t:ℝ): Plane.Flux.tree r K F (coin (t:ℂ))=0:= by
    ext l; unfold Plane.Flux.tree; rw [ show Plane.Flux.attaches r K F (coin (t:ℂ))=0 from funext fun l=>funext fun v=>by simp [Plane.Flux.attaches,coin] ]; exact map_zero ( allocate ..)
lemma noL (t:ℝ)(q:Rip G){F:Flats G}: TreeN q F (baseFlat G t)=0:= by
    induction F using Finsupp.induction_linear with
    | zero=> simp
    | add i j hi hj=> simp only [map_add,LinearMap.add_apply,hi,hj,add_zero]
    | single i x=> rw [baseFlat, Park.zap ]; rw [ show tapeB (Rock.Oceans.squad q) x (Brace G t)=(0:Coat G) from funext fun x=> funext fun m=> tree_p .. ]; simp
-- Cost handles kernel.Pact
lemma laterd (t:ℝ): Pact (step0 G (baseFlat G t)) 0:= by
    obtain ⟨hc,h0⟩:= badge (G:=G) t; obtain ht:= Cap0.heap.single h0 0; apply pact0; exact ⟨ ((0:ℤ)-2),by decide,capC 0 (clockCap ht) ( clockMoon ht ) ( c_bo 0 )⟩
lemma stays_p (t:ℝ) (p:ℝ) (q:ℝ): Shine.Lift (Parade (x₀ t) 0 p q) ( pawnMob G t ):=by rw [baseFlat,pureP (h:= (badge _).1)]; exact Shine.Lift.stays ( Pace.priceV (G:=G) (fun _=> lease t))
lemma once (t:ℝ) (B: T ( Flats G )): comet 0 0 B (UnitF (Brace G t)) (UnitF (baseFlat G t)) 0:=by
    have hp(i:ℕ): platform B i (UnitF (x₀ t))=0:= by unfold platform; refine Finset.sum_eq_zero (fun n _=>?_); unfold UnitF; split; exact noL t _; exact map_zero _
    intro i; unfold PathD; rw [hp i]; rcases i with _|i; swap; · exact zero_sing _
    have hv:= badge (G:=G) t; refine ⟨⟨0,?_,Cap0.heap.single hv.2 0,Cap0.zero⟩,False.elim⟩; change Joint 0 (0+step0 G (x₀ t)) (x₀ t) (Brace G t) 0; rw [zero_add]; apply Joint.via (J:=0) _ (pact_sym (laterd t)); -- record add order.Zero
    refine ⟨ vibe_root hv.1, fun i j=> ⟨_, stays_p ..⟩, ( Moony.toast (clockMoon (Cap0.heap.single hv.2 0))), (cone G).zero_mem, mer.zero, fun _=> Home.zero 0,?_⟩; rw [add_zero]; exact sip_root hv.1
end YM.FVA2.Position.Ace
