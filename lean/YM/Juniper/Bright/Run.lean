import YM.Juniper.Bright.Pact
/-! # Period enlargement • physical YES for whole book. Integer addresses. -/
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
variable {G: Gauge} {c f c' f' L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
    {S': StepData c' f'} {T': Tube G S'} {R' : Rep G f'}
      {W μ x C C' s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R} {I' :Cash W x μ L Q o C' T' R'}
      {j n k:ℕ}
open Shelf
variable (Y:Shelf I n) (U:Shelf I' n) (k)
def beaconLeft (H:Cash W x μ L Q o C T R)(χ:Chi)(z:H.fragrances) (V:Config G c):= -(↑(Captain.reachability z).card:ℝ)⁻¹*stream H χ V z
def Ledger (χ:Chi)(a:Site c) (V:Config G c):= ∑ z∈ (Y.slate k).filter (fun z=> a∈ Captain.reachability z), beaconLeft I χ z V
namespace Lamp
variable {Y U k} {a:Site c}{g:Site c → Site c'} (h:Lamp k Y U a g)
local notation "Z"=> Y.Window k a
local notation "K"=> U.Window k (g a)
local notation "π"=> h.π
lemma there {t: I.fragrances} (ht:t∈Y.slate k) (hp:a∈ Captain.reachability t) :∃ s: Tuple I'.ThinP t.1,
    Sigma.mk t.1 s∈U.slate k ∧ g a∈unionOf I'.smallAt s∧∀ i,(s i).val=(t.2 i).val.image h.π:=by
  have hh:= (Shelf.in_slate _).mp ht; have hw i:= Y.resident hh a hp i
  let A i:= U.paper ((h.seating (hw i)).1 (hh.themes i)); have ha i:(A i).val= (t.2 i).val.image h.π:=rfl
  exact ⟨A,(Shelf.in_slate _).mpr ⟨hh.height,fun i=> (h.seating (hw i)).1 (hh.themes i), (h.mate hw ha) ▸ hh.moves⟩,(h.inset hw ha).1 hp, ha⟩
lemma here {t: I'.fragrances}(ht: t∈U.slate k)(hp:g a∈ Captain.reachability t):∃ s: Tuple I.ThinP t.1, Sigma.mk t.1 s∈Y.slate k ∧ a∈unionOf I.smallAt s ∧∀ i, (s i).val.image h.π=(t.2 i).val:=by
  have hh:= (Shelf.in_slate _).mp ht; have hw i:= U.resident hh (g a) hp i
  choose v hv hz using fun i=> h.back_frame _ (hw i)
  have hH i:Y.theme (v i) k:= (h.seating (hv i)).2 (by rw [hz i]; exact hh.themes i)
  let A i:= Y.paper (hH i); have ha i:(t.2 i).val=(A i).val.image h.π:= (hz i).symm
  have ht i:(A i).val⊆ Z:= hv i
  exact ⟨A, (Shelf.in_slate _).mpr ⟨hh.height,hH,(h.mate ht ha).symm ▸ hh.moves⟩,(h.inset ht ha).2 hp,fun i=>(ha i).symm⟩
-- extra assumptions as cost localized true block entries. Not a mere valuation on prices. Instantiated next.
lemma compare (V: Config G c) (W: Config G c')
    (hc : ∀ (t : I.ThinP),Y.theme t.val k→ t.val⊆ Z →∀ s:I'.ThinP,s.val=t.val.image h.π→ leaflet I χ V t=leaflet I' χ W s) :
    Bright.Ledger k Y χ a V= Bright.Ledger k U χ (g a) W:=by
   let X:= (Y.slate k).filter (fun z=> a∈Captain.reachability z)
   let Ω:= (U.slate k).filter (fun z=> g a∈Captain.reachability z)
   let F (i) (b:i∈X) := h.there (mem_filter.mp b).1 (mem_filter.mp b).2|>.choose
   have hv (i:I.fragrances) (b:i∈X) : Sigma.mk i.fst (F i b)∈ Ω ∧ ∀ j, (F i b j).val= (i.2 j).val.image π:= by
     obtain ⟨ht,hp,hr⟩:= h.there (mem_filter.mp b).1 (mem_filter.mp b).2|>.choose_spec; exact ⟨mem_filter.mpr ⟨ht,hp⟩,hr⟩
   have hV (i:I.fragrances) (he:i∈X) : Y.Charming k i:=(Shelf.in_slate _).mp (mem_filter.mp he).1
   have hz (i:I.fragrances) (b:i∈X) j:= Y.resident (hV i b) a (mem_filter.mp b).2 j
   refine Finset.sum_bij (fun x he=> Sigma.mk x.fst (F x he)) (fun i hi=> (hv i hi).1) ?_ ?_ ?_
   · rintro ⟨i,t⟩ hi ⟨j,s⟩ hj he
     have hX:= congr_arg Sigma.fst he; change i=j at hX; subst j
     have he : F (Sigma.mk i t) hi=F (Sigma.mk i s) hj:=Sigma.mk.inj_iff.mp he|>.2|>eq_of_heq
     refine congr_arg (Sigma.mk i) (funext fun v=> ?_)
     exact (h.inv (hz _ hi v) (hz _ hj v) ((hv _ hi).2 v).symm ((hv _ hj).2 v).symm).2 (congr_fun he v)
   · intro i hi; obtain ⟨v,hv₀,hx,hM⟩:= h.here (mem_filter.mp hi).1 (mem_filter.mp hi).2
     have hx0 : Sigma.mk i.fst v∈X:=mem_filter.mpr ⟨hv₀,hx⟩
     exact ⟨_, hx0, congr_arg (Sigma.mk i.fst) (funext fun j=> show F _ hx0 j=i.2 j from Subtype.ext (((hv _ hx0).2 j).trans (hM j)))⟩
   intro i hi
   let f' := F i hi; have hM:= h.mate (hz i hi) ((hv i hi).2)
   have ht j:= hc _ ((hV i hi).themes j) (hz i hi j) (f' j) ((hv i hi).2 j)
   have hp := h.ticketed (hz i hi) ((hv i hi).2)
   symm; change -((↑(unionOf I'.smallAt f').card:ℝ)⁻¹) * _= _ -- whose scope?
   unfold beaconLeft Captain.reachability stream Gas.term; dsimp [f']; rw [hp,← hM]
   apply congr_arg₂ HMul.hMul
   · rw [Finset.card_image_of_injOn (h.tours.mono ?_)]
     exact coe_subset.mpr ((Y.fit (hV i hi) a (mem_filter.mp hi).2).trans (fun y hv=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hv).trans (Nat.le_add_right ..))))
   congr 2; exact prod_congr rfl fun i _=> (ht i).symm
end Lamp
end YM.Juniper.Bright
