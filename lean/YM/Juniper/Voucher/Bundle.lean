import YM.Juniper.Voucher.Awe
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Voucher
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c: Side} (P X Y : Listing G c) (p x y:Collection.Source G c)
local notation "A"=> numbering (ℕ ⊕ ℕ)
abbrev package (P X Y : Listing G c) : Listing G c := ⟨Sum.elim X.reg Y.reg ∘ numbering (ℕ ⊕ ℕ),P.hard⟩
abbrev stack (p x y:Collection.Source G c) : Collection.Source G c := ⟨Sum.elim x.logRead y.logRead ∘ numbering (ℕ⊕ℕ),p.hardRead⟩

variable (F:Config G c)(B:BudgetPoint)
variable {p X Y x y B}{σ τ δ : ℝ}(hx: Meadow.Budget B X.reg x.logRead σ)(hy: Meadow.Budget B Y.reg y.logRead τ)
include hx hy
lemma payroll_pack : Meadow.Budget B (package P X Y).reg (stack p x y).logRead (σ+τ):= by
  obtain ⟨f,hf,hF⟩:=hx; obtain ⟨g,hg,hG⟩:=hy
  let v:=Sum.elim f g; refine ⟨v∘ A,fun i=>Cost.equiv (numbering (ℕ ⊕ ℕ)) (Cost.sum (f:=fun j : ℕ⊕ℕ=> if ((Sum.elim X.reg Y.reg) j|>.site)=i then v j * Real.exp (preExponent B * coverNumber B.B (Sum.elim X.reg Y.reg j).support) else 0) (hf i) (hg i)),?_⟩
  intro i; dsimp only [package,stack, comp_apply]; cases A i; exact hF _; exact hG _

lemma additive_pack : ((package P X Y).read (stack p x y)).additive B F=(X.read x).additive B F+(Y.read y).additive B F:= by
  let g j:= Sum.elim (fun i=>(X.read x).regularOccurrence B i F) (fun i=>(Y.read y).regularOccurrence B i F) j
  rw [Activities.additive,show (fun i=> ((package P X Y).read (stack p x y)).regularOccurrence B i F)= (fun i : ℕ=> g (A i)) from ?_]
  change ∑' i,g (A i)= _; rw [Equiv.tsum_eq,Summable.tsum_sum (f:=g) (Marlin.stashes B X x F hx) (Marlin.stashes B Y y F hy)]; rfl
  funext i; unfold Activities.regularOccurrence; change masked _ (Sum.elim X.reg Y.reg (A i)).support (Sum.elim x.logRead y.logRead (A i)) F= g (A i); cases A i <;> rfl
omit hx hy
-- enough with ONE joint REG perm, no identity of hard inventories needed at prediction surface
abbrev EPerm (Y:Listing G c) (v:Collection.Source G c) (s: Signed) (b:Site c) (π : Equiv.Perm ℕ) :=
     (∀ i,(Y.reg (π i)).site=Lattice.affine s b (Y.reg i).site)∧(∀ i,(Y.reg (π i)).support=(Y.reg i).support.image (Lattice.affine s b))∧ ∀ i U,v.logRead (π i) U=v.logRead i (pull s b U)
variable {s:Signed}{b:Site c}{π φ:Equiv.Perm ℕ}
def carryPack (p m:Equiv.Perm ℕ) : Equiv.Perm ℕ:= congo (numbering (ℕ ⊕ ℕ)) (Equiv.sumCongr p m)
lemma stackP (hu:EPerm X x s b π)(hv:EPerm Y y s b φ): EPerm (package P X Y) (stack p x y) s b (carryPack π φ):=by
   let v:= carryPack π φ; let U:= Equiv.sumCongr π φ; let f:= Sum.elim X.reg Y.reg; let g:= Sum.elim x.logRead y.logRead
   have he i: (f (U i)).site=Lattice.affine s b (f i).site ∧ (f (U i)).support=(f i).support.image (Lattice.affine s b) ∧ ∀ V,g (U i) V=g i (pull s b V):= by cases i; exact ⟨hu.1 _,hu.2.1 _,hu.2.2 _⟩; exact ⟨hv.1 _,hv.2.1 _,hv.2.2 _⟩
   have hh(i): A (v i)=U (A i):= perch ..
   refine ⟨fun i=>?_,fun i=> ?_,fun i V=>?_⟩
   · exact (show (f (A (v i))).site=_ from (hh i).symm ▸ (he (A i)).1)
   · exact (show (f (A (v i))).support=_ from (hh i).symm ▸ (he (A i)).2.1)
   exact (show g (A (v i)) V= _ from (hh i).symm ▸ (he (A i)).2.2 V)

def underPack (H:(P.read p).Moves s b) {u:Equiv.Perm ℕ} (hV: EPerm (package P X Y) (stack p x y) s b u): ((package P X Y).read (stack p x y)).Moves s b := ⟨u,H.kp,hV.1,hV.2.1,H.forced_support,H.forced_inventory,H.forced_tests,hV.2.2,H.valuesK⟩
-- phase inventory on paper E predictor (keeps true hard forcibly)
variable {z:Collection.Source G c}
lemma EPerm.subtract (h:EPerm X x s b π)(he:EPerm X z s b π) : EPerm X (x-z) s b π:= ⟨h.1,h.2.1,fun i U=>congr_arg₂ (·-·) (h.2.2 i U) (he.2.2 i U)⟩
lemma EPerm.fromM (H: (X.read x).Moves s b) : EPerm X x s b H.ep:=⟨H.reg_site,H.reg_support,H.valuesE⟩
include hx in
lemma additive_sub (h: Meadow.Budget B X.reg z.logRead δ): (X.read (x-z)).additive B F = (X.read x).additive B F-(X.read z).additive B F:= by
   unfold Activities.additive; rw [← (Marlin.stashes B X x F hx).tsum_sub (Marlin.stashes B X z F h)]; apply tsum_congr; intro i; unfold Activities.regularOccurrence; unfold masked Set.indicator; dsimp only[Listing.read]; split <;> first |rfl| abel
end YM.Juniper.Voucher
