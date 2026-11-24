import YM.MSbar.Mosaic.Lease
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Measuring
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(R: Rep G f)(J:Voice G)
variable (i:Site f)(x:ℝ)
local notation "G'"=> Key F G
noncomputable def closeN (x:ℝ):= (radiusB x)^3
noncomputable def spotN (x:ℝ):= (radiusB x)^4
noncomputable def boxX (x:ℝ)(i:Site f):Support f:=halo (spotN x) {i}
noncomputable def boxY (x:ℝ)(i:Site f): Support f:=halo (2*voyageB x+8) (boxX x i)
noncomputable def boxK (x:ℝ):= skirt (spotN x)*skirt (2*voyageB x+8)
noncomputable def boxL (x:ℝ)(P:Patch):=boxK x*skirt (4*P.L.val+8)
lemma caseX : (boxX x i).card ≤ skirt (spotN x):=by simpa only [boxX,skirt,card_singleton,one_mul] using Corona.halo_size ({i}:Support f) (spotN x)
lemma caseY : (boxY x i).card ≤ boxK x:=by unfold boxY; apply le_trans (Corona.halo_size ..); exact Nat.mul_le_mul_right _ (caseX ..)
lemma caseL : coverNumber R.p.B (youth F (boxY x i)) ≤ boxL x S.patch :=by
     let X:= youth F (boxY x i); have hv:X.card ≤ boxL x S.patch:= le_trans (show X.card≤ _ from Corona.halo_size (boxY x i) (4*S.patch.L.val+8)) (Nat.mul_le_mul_right _ (caseY ..)); apply le_trans _ hv; have h(X:Support f)(n:ℕ)(h: Corona.Ships X 1): Corona.Ships (halo n X) 1 := Corona.ship_halo n fun i hi j hj=>Relation.ReflTransGen.mono (fun u v (ht : Corona.Touch X 1 u v)=>⟨ht.1,ht.2.1,(ht.2.2).trans (by omega)⟩) i _ (h i hi j hj)
     apply Corona.list_cost _ (D:=X); refine ⟨halo_subset .., h X _ (h _ _ (h _ _ (Corona.ship_halo (spotN x) fun i hi j hj=> ?_)))⟩; rw [Finset.mem_singleton.mp hi,Finset.mem_singleton.mp hj]
local notation "Φ"=> address F G
lemma housing(y:Key F G)(h:y∉ Set.range (includeX (G:=G) F (boxX x i))) : spotN x ≤ separation (address F G (Sum.inr y)) i:=by
    by_contra! he; have hp:y.1.val.1∈boxX x i:=halo_spec .. |>.mpr ⟨i,mem_singleton_self _,(separation_comm ..).le.trans he.le⟩; exact h ⟨(⟨y.1,mem_filter.mpr ⟨mem_univ _,hp⟩⟩,y.2),rfl⟩
local notation "X"=>Primary c G
lemma zoneM (L:List (Primary c G))(hB:ranged F L i (spotN x)): ∀ j∈L,S.ratio.embed (Measuring.chart c G j)∈ boxX x i:= fun j hj=> halo_spec .. |>.mpr ⟨_,mem_singleton_self _,hB j hj⟩
-- ranged measure id:∥parent distance∥ grows.L; include apex lift.
lemma zoner (L:List (Primary c G))(v:Primary c G)(hx:Bristol.peaks (Measuring.chart c G) (v::L)≤ closeN x): ranged F (v::L) (S.ratio.embed (Measuring.chart c G v)) (S.patch.L.val*closeN x):=by
     intro j hj; let a:=Measuring.chart c G j; let v':=Measuring.chart c G v; unfold address; change separation (S.ratio.embed v') (S.ratio.embed a) ≤ _ 
     let Ge := Whisk.zone (Measuring.chart c G) ∅ (v::L); have he(i:Primary c G)(hh:i∈v::L): Measuring.chart _ _ i∈ Ge:= mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hh,rfl⟩))
     let q:=S.ratio; refine le_trans (b:=q.count.val*(separation v' a)) ?_ (Nat.mul_le_mul_left S.patch.L.val ((curve (he v (List.mem_cons_self ..)) (he j hj)).trans hx)); change separation (q.embed v') (q.embed a)≤ _; unfold separation; rw [← q.root_embed, ← q.root_embed, ← map_sub,q.root_embed]; unfold pdist; refine Finset.sup_le fun i _=>?_ ; rw [q.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (component_le (v'-a) i)

variable (A B:Stage)(p:Palisade)(P:Patch)(T:KernelChoices)(hg:Clear G J)(g:G.Simple)
local notation "U"=> (fun x=> tip G P.L x)
include hg g
lemma earned (d v:ℝ)(M:ℕ) : ∀ᶠ x in atTop,Credit P T G J p A B M d x v (boxK (tip G P.L x)) (boxL (tip G P.L x) P):=by
     let h:= Beads G P; have hh:= Heath.Stock.Beam.shore P.L G; have ht:Heath.Stock.Beam G P.L (fun x=> (spotN (tip G P.L x):ℝ)) :=by unfold spotN; simp only [Nat.cast_pow]; exact hh.power 4
     have hb:Heath.Stock.Beam G P.L (fun x=> ((2*voyageB (tip G P.L x)+8:ℕ):ℝ)):=by push_cast; exact ((Heath.Stock.Beam.coin 2|>.mul h).add (Heath.Stock.Beam.coin 8)) -- syntax
     let L:= boxK ∘ U; let f'(x):= boxL (U x) P; have hp:Heath.Stock.Beam G P.L (fun x=>(L x:ℝ)):=by
             change Heath.Stock.Beam G P.L (fun x:ℝ=> ((skirt (spotN (tip G P.L x))*skirt (2*voyageB (tip G P.L x)+8):ℕ):ℝ)) 
             simp only [Nat.cast_mul]; exact Heath.Stock.Beam.mul (chargesA P _ ht) (chargesA P _ hb)
     apply honored P T p J A B hg d v L f' hp; unfold f' boxL; simp only [Nat.cast_mul]; exact hp.mul (Beam.coin _)
end YM.MSbar.Mosaic
