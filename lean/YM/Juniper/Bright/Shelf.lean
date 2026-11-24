import YM.Juniper.Bright.Billable
/-!
 # Local windows for interpolation gluing of arbitrary ARITY jets

 Low-order Meadow ports using new local-enrollment partition at a marked
 point, not requiring potentially gigantic simultaneous bij. Reuse components
 and keep all incidence labels, no cancellation across masks here yet.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
      {W μ x C s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R}
      {j n k:ℕ} {V : Config G c}

structure Shelf (I:Cash W x μ L Q o C T R)(r:ℕ) where
  binders : Finset (Head S)
  presents (p: Molecule S) : p⊆binders → (roster p).flags=∅
  pin : Head S→Site c
  pertinent (p) : p∈binders → pin p ∈ I.supportP p
  halls (p) : p∈binders → I.supportP p⊆ neighbors r (pin p)
namespace Shelf
variable (Y:Shelf I n)
def theme (p: Molecule S) (k:ℕ): Prop := Ac.Spark I.supportP p ∧ p.card≤ k ∧ p ⊆ Y.binders
lemma enroll {p:Molecule S}(h:Y.theme p k): (I.unionP p).Nonempty ∧ (roster p).flags=∅:=by
  obtain ⟨i,hi⟩:=h.1.1; exact ⟨⟨_,mem_biUnion.mpr ⟨i,hi,Y.pertinent _ (h.2.2 hi)⟩⟩,Y.presents p h.2.2⟩
def paper {p:Molecule S}(h:Y.theme p k): I.ThinP := ⟨p,Y.enroll h⟩
variable (k)
structure Charming (z:I.fragrances) : Prop where
  height : z.fst ≤ k
  themes i : Y.theme (z.snd i).val k
  moves : coefficient I.seam z.snd ≠0
lemma finitude : {z:I.fragrances| Y.Charming k z}.Finite:= by
   let f := Y.binders; let S : Set I.ThinP := Subtype.val ⁻¹' (↑(Finset.powerset f): Set (Molecule _))
   have h : S.Finite:= ((Finset.powerset f).finite_toSet).preimage Subtype.val_injective.injOn
   let T:= (Finset.range (k+1)).sigma fun i:ℕ=> Fintype.piFinset (fun _ : Option (Fin i)=> h.toFinset)
   refine Finset.finite_toSet T |>.subset fun z hz=> ?_
   rcases z with ⟨i,v⟩
   change Y.Charming k ⟨i,v⟩ at hz; apply mem_sigma.mpr
   refine ⟨mem_range.mpr (Nat.lt_succ_of_le hz.height), Fintype.mem_piFinset.mpr (fun j=> ?_) ⟩
   exact h.mem_toFinset.mpr (show (v j).val ∈ f.powerset from mem_powerset.mpr (hz.themes j).2.2)
def slate : Finset I.fragrances := (Y.finitude k).toFinset
variable {k} {z:I.fragrances}
lemma in_slate : z∈ Y.slate k ↔ Y.Charming k z:= Set.Finite.mem_toFinset ..
lemma charges (h:Y.Charming k z)(i) : coverNumber n (I.unionP (z.2 i).val) ≤ k:= by
  have hX:= (h.themes i).1; apply le_trans (Ac.cover _ _ hX)
  have hh: ∀ j∈ (z.2 i).val,coverNumber n (I.supportP j) ≤ 1:= fun j hj=> by
    let X:= Y.pin j; have he:neighbors n X=halo n ({X}:Finset (Site c)):=by ext i; simp only [halo_spec,neighbors_mem,mem_singleton]; grind
    have hp:covers n (I.supportP j) ({X}:Finset (Site c)):=⟨he ▸ Y.halls _ ((h.themes i).2.2 hj), Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  exact le_trans (Finset.sum_le_sum (hh)) (by simp [(h.themes i).2.1])
lemma width (h:Y.Charming k z): coverNumber n (Captain.reachability z) ≤ (k+1)*k:= by
    have hx:= connected_pay I.seam I.smallAt n I.testS z.2 zero_le_one h.moves
    unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx
    apply (Nat.cast_le (α:=ℝ)).mp
    push_cast; apply hx.trans; apply le_trans (Finset.sum_le_sum (g:=fun _=> (k:ℝ)) (fun i _=> by exact_mod_cast Y.charges h i))
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; push_cast; gcongr; exact h.height
-- polynomial studio for *all* arities. d(f): includes buffer for outgoing E movement.
def terrace (n k:ℕ) := (k+1)*k*(4*n+2)+4*n+1
lemma fit (h:Y.Charming k z)(p:Site c)(hp:p∈ Captain.reachability z): Captain.reachability z⊆ neighbors (terrace n k) p:= by
    intro i hi; apply (neighbors_mem ..).2
    have H:= Y.width h
    apply (Corona.extent _ _ hp hi).trans; unfold terrace; nlinarith only [Nat.mul_le_mul_right (4*n+2) H]
def Window (k:ℕ)(p: Site c): Finset (Head S) := Y.binders.filter fun i=> Y.pin i∈neighbors (terrace n k) p
lemma resident (h:Y.Charming k z)(p : Site c)(hp : p∈Captain.reachability z)(i): (z.2 i).val ⊆ Y.Window k p := by
    intro j hj; have hy:= (h.themes i).2.2 hj; apply mem_filter.mpr; refine ⟨hy,Y.fit h p hp (subset_biUnion_of_mem (I.smallAt ∘ z.2) (mem_univ i) (?_ : _∈ I.smallAt (z.2 i)))⟩
    exact mem_biUnion.mpr ⟨_,hj,Y.pertinent j hy⟩
lemma patio (w : Molecule S)(p : Site c)(hp:w⊆ Y.Window k p): I.unionP w⊆ neighbors (terrace n k+n) p:= by
    intro i hi; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp hi; obtain ⟨ht,hf⟩:= mem_filter.mp (hp hj); apply (neighbors_mem ..).2; exact (separation_triangle p (Y.pin j) i).trans (add_le_add ((neighbors_mem ..).1 hf) ((neighbors_mem ..).1 (Y.halls _ ht hi)))
lemma ensured (z:I.fragrances)(hx:stream I χ V z ≠0) (h':¬ Bright.high I k z) (hp:∀ i,(z.2 i).val⊆Y.binders) : Y.Charming k z:= by
  have hk:Height.breadth I z≤ k:= le_trans (Nat.le_add_right ..) (le_of_lt (lt_of_not_ge (fun h=> h' (Or.inl h)))) -- param e
  refine ⟨?_,fun i=> ⟨(Bright.merit I z hx i).1,?_,hp i⟩, Bright.profitable I z hx⟩
  · exact (Nat.le_succ _).trans ((Beam.on_one z (fun i=> card_pos.mpr (Bright.merit I z hx i).1.1)).trans hk)
  exact ((single_le_sum (f:=fun i=> (z.snd i).val.card) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans hk)
end Shelf
end YM.Juniper.Bright
