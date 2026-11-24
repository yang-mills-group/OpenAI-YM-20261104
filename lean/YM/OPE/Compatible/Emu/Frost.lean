import YM.OPE.Compatible.Emu.World
/-!
# Annulus receipts. All walks paid in radius not period. L-Aspects in vertices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}
noncomputable def crossV (S:Finset Cover): Finset (Edge Cover):=(S ×ˢ (univ:Finset Axis)).filter fun i=>dotUp i∈S
noncomputable def galaxy (r b:ℕ):Finset Cover:= Lattice.box b \ Lattice.box r
lemma cross_def (x:Edge Cover):x∈crossV S↔x.1∈ S ∧ dotUp x ∈ S:=by rw[crossV,Finset.mem_filter,mem_product, and_iff_left (mem_univ _)]
lemma cross_amt (S:Finset Cover): (crossV S).card ≤ S.card*4:=(card_filter_le ..).trans (by rw [card_product,card_univ]; exact le_rfl)
lemma cross_mono {T:Finset Cover}(h:S ⊆ T):crossV S⊆crossV T:=fun x hx=> (cross_def x).mpr ⟨h ((cross_def x).mp hx|>.1),h ((cross_def x).mp hx|>.2)⟩
lemma scall (h:r < b): StepsL.RingP b⊆ galaxy r b:=by
       intro i hi; obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (show b>0 by omega)); rw [ring_up] at hi; obtain ⟨hx,hp⟩:= mem_sdiff.mp hi; exact mem_sdiff.mpr ⟨hx,fun hz=>hp (taller (by omega) hz)⟩
lemma annex (x:Cover)(i:Axis)(he:r < (x i).natAbs):bed (Lattice.box b) i (x i) ⊆ galaxy r b:=by
       intro y hy; obtain ⟨hz,h⟩:=mem_filter.mp hy; change y i=x i at h; refine mem_sdiff.mpr ⟨hz,fun ht=>?_⟩; obtain ⟨hV,hz⟩:=box_test.mp ht; specialize hV i; specialize hz i; omega
lemma hoof (x:Cover)(h: x∉Lattice.box r):∃ i:Axis,r<(x i).natAbs:=by
       by_contra he; apply h; push Not at he; rw[box_test]; constructor<;> intro i<;> specialize he i<;>omega
lemma roc (h:r < b) : StepsL.anchorX b∈galaxy r b:= scall h (lodger b)
lemma spaced (h:r < b)(x:Cover)(hp:x∈galaxy r b): StepsL x (StepsL.anchorX b) (galaxy r b) (40*b) ∧ StepsL (StepsL.anchorX b) x (galaxy r b) (40*b):=by
        obtain ⟨hx,hp⟩:=mem_sdiff.mp hp; obtain ⟨i,hi⟩:=hoof x hp; obtain ⟨a,ha⟩:=alter i; let z:=dye x a ↑b; have hv:z a=↑b:=update_self ..; have hb: z∈ Lattice.box b:= painted x _ _ hx (by omega); have hz:z∈StepsL.RingP b:= mem_filter.mpr ⟨hb,a,by omega⟩; have he:z i=x i:=update_of_ne ha ..; refine ⟨lend (both (lend (ceiling hx hb i he.symm) (annex x i hi) le_rfl) ((crown hz (lodger _)).lend (scall h) le_rfl)) (by rfl) (by omega),?_⟩; exact lend (both (lend (crown (lodger _) hz) (scall h) le_rfl) (lend (ceiling hb hx i he) (annex z i (he.symm ▸ hi)) le_rfl)) (by rfl) (by omega)
-- projection endpoints.Our IE.
variable {E:Type*}
noncomputable abbrev bark (b:ℕ):=crossV (Lattice.box b)
noncomputable abbrev leash (r b:ℕ):=crossV (galaxy r b)
lemma surf (h:r<b):Delta r⊆bark b:=fun x hx=> (cross_def x).mpr ⟨taller (by omega) (arcP hx).1,taller (by omega) (arcP hx).2⟩
lemma cure (r b:ℕ):leash r b⊆bark b:=cross_mono (Finset.sdiff_subset)
lemma beat (r b:ℕ): Disjoint (leash r b) (Delta r):=by refine Finset.disjoint_left.mpr fun i hi hp=>?_ ; obtain ⟨hx,hh⟩:= (cross_def i).mp hi; exact ((deck _).mp hp).elim (mem_sdiff.mp hx).2 (mem_sdiff.mp hh).2
lemma tons (x:Edge Cover):x∈leash r b↔x∈bark b ∧ x∉Delta r:=by
       refine ⟨fun hi=> ⟨cure _ _ hi,(Finset.disjoint_left.mp (beat _ _) hi)⟩,fun ⟨hx,hv⟩=>?_⟩; obtain ⟨ht,hS⟩:= (cross_def _).mp hx; apply (cross_def x).mpr; exact ⟨mem_sdiff.mpr ⟨ht,fun hp=>hv ((deck _).mpr (Or.inl hp))⟩,mem_sdiff.mpr ⟨hS,fun hp=> hv ((deck _).mpr (Or.inr hp))⟩⟩
-- lesson
lemma setNorth (i:Edge Cover)(h:i∈crossV S)(he:S⊆Lattice.box b):i.1∈ Lattice.box b:= he ((cross_def i).mp h|>.1)
lemma berth_dir {x y:Edge Cover}(h:Board n b)(hx:x∈bark b)(hy:y∈bark b)(hp:Moor x n=Moor y n):x=y:=Prod.ext (berthInj h _ _ ((cross_def _).mp hx|>.1) ((cross_def _).mp hy|>.1) (congrArg Prod.fst hp)) (congrArg (fun x:Edge (Site n)=>x.2) hp)
noncomputable def BlurD (G:Gauge)(S:Finset (Edge Cover))(n:Side):= dip (fun i:↥S=>i.val) n 0 (G:=G)
variable (p:Finset (Edge Cover)) (x:Bid.Dir G n)
lemma echoP (i:↥p): BlurD G p n x i=x (arkE (Moor i.val n)):=by change x (sett n 0 i.val)=_; rw[ark_sett]
section
variable (F:Type)[Zero F]
variable {q:Finset (Edge Cover)} (h:Board n b)(ht:q⊆bark b)
noncomputable def tipQ (q:Finset (Edge Cover))(k:∀ i∈q,∀ j∈q,Moor i n=Moor j n→i=j): ↥q ↪ Body 1 n := ⟨fun i=> arkE (Moor i.val n), fun i j hp=>Subtype.ext (k _ i.property _ j.property (arkInj hp))⟩
noncomputable def mote:=tipQ q (fun _ ha _ hh hp=>berth_dir h (ht ha) (ht hh) hp)
end
end YM.OPE.Merchant
