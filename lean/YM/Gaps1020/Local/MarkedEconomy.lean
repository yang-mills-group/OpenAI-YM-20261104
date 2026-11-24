import YM.Gaps1020.Local.MarkedPermit
import YM.Gaps1020.Local.MarkedFunds
import YM.Gaps1020.Local.Sales
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
variable {ι:Type}[Fintype ι]
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves
variable (N:Captain H j C' d v Y A b r B q k χ)(U:ι→Team R)(M':ι→Leaf R)
    (rA:ι→ℝ)(X:Utopia H j v d r C' χ)
local notation "I'" => Tickets (Palette.sign M' S)
-- pays on summed derivatives over switches. keep in original H with thermal inflation
-- many legs inside p allowed, no arity/cancellation factors.
def scalarWeight {w:ι→Head S}(i:Tickets w):ℝ:=∏ j∈i.val,rA j
def sumWeight (M:ℕ)(ρ Z:ℝ)(p:H.ThinP):=∑ i:I',scalarWeight rA i*reserveBy N p (Palette.team M' i) ρ Z M
omit [Fintype ι] in
lemma scalarWeight0 {w:ι→Head S}(i:Tickets w)(h:∀ i, 0≤rA i):0≤ scalarWeight rA i:= prod_nonneg fun i _=> h i
lemma sumWeight0 (M:ℕ)(ρ Z:ℝ)(hp:0≤ρ)(hz:0≤Z)(hc:∀ i, 0≤rA i)(p:H.ThinP):0≤ sumWeight N M' rA M ρ Z p := sum_nonneg fun i _=>mul_nonneg (scalarWeight0 rA i hc) (reserve0 N p _ Z hp hz M)
local notation "q0" => Q.costs L μ R.beta s C'
local notation "S'" => swing Q L μ R.beta s C'
local notation "T'" => steamP S (Q.costs L μ R.beta s C')
local notation "D"=> ConnectedActivityE6.lengths T R
local notation "c0" => radiusB s

lemma sumPower (p:Molecule S) :
    ∑ i:I',scalarWeight rA i * earnedBy p (Palette.team M' i) X k= Mixed.selected S Q.halo c0 S' H.birth (Thermal.together M' rA X.flair) D T' 0 k 0 0 p :=by
   unfold earnedBy Mixed.selected
   by_cases hp:H.ticketsP 0 0 0 p
   swap; · rw [if_neg (show ¬Mixed.Allowed S Q.halo c0 S' H.birth D 0 0 0 p from hp)]; apply sum_eq_zero; intro i _; rw [if_neg (fun h=> hp h.1),mul_zero]
   let Y i:= X.fare i + Tickets.extra (Palette.sign M' S) (wages M' rA) i
   have hY (i:Head S) : Y i=Mixed.costs S Q.halo c0 T' (Thermal.together M' rA X.flair) i:=by
       rcases i with i|i
       · unfold Y Tickets.extra; rw [sum_eq_zero, add_zero]; · rfl
         intro j _; exact if_neg (fun h=> by have hf:=(show .inr _ = Palette.sign M' S j from Daisy.sparkPath ..).trans h; contradiction)
       unfold Y Tickets.extra Utopia.fare stout Mixed.costs Thermal.together Tickets.extra
       dsimp only [Sum.elim]; simp_rw [← show ∀ j, (.inr (Palette.mark M' (c:=c) j):Head S)=Palette.sign M' S j from fun j=> Daisy.sparkPath ..]; simp only [Sum.inr.injEq]; rfl
   rw [if_pos (show Allowed S Q.halo c0 S' H.birth D 0 0 0 p from hp)]
   unfold Mixed.Price; simp_rw [← hY]; unfold Y; rw [Tickets.expanded, Finset.sum_mul]
   apply sum_congr rfl; intro i _
   rw [label M' i]; by_cases he:i.reach⊆p; swap; · rw [if_neg he,if_neg (fun h=>he h.2),zero_mul,mul_zero]
   rw [if_pos he, if_pos ⟨hp,he⟩,Palette.worth]; unfold Palette.wages; rw [Finset.prod_mul_distrib]; unfold others; rw [Palette.label]
   change _= _*(1+H.shapeW p)^k; unfold scalarWeight; ring
variable {Z:ℝ}
omit [Fintype ι] in
lemma pumpMix (p:Molecule S)(U:Team R)(h:WarnBudget Z X)(hZ:1≤ Z) :
    earnedBy p U (pump h hZ) k=Z^(blaze p).card*earnedBy p U X k:=by
   unfold earnedBy; split; next h'=> rw [Utopia.remixes (pump h hZ),X.remixes, remainBlaze]; rw [show (pump h hZ).rad= Z*X.rad from rfl]; unfold Utopia.tag pump; simp only; ring
   next h'=>rw [mul_zero]

variable (hc: Thermal.BuysMix M' H rA)(he:(swing Q L μ R.beta s C').Buy S.patch.L Q.halo (radiusB s))(hρ:0<ρ)
    (hd: Trees.degreePrice (radiusB s) (ρ*(swing Q L μ 1 s 0).rootHit) Q.δ≤1/2)(hv:1≤ Z)
def swingTab (Q:ConnectedActivityE6.Target G P)(L:Side)(μ s ρ:ℝ)(m:ℕ)(y:ℝ)(k:ℕ):= extract Q.ε k y (Q.mark L μ s*m) * treeYield (ρ*(swing Q L μ 1 s 0).rootHit) (1/2) 0
include hc he hρ hd
lemma existsHit (m k':ℕ)(hp':k'=k)(y:ℝ) : Ac.Hit H.smallAt c0 (fun p=> if y≤H.shapeW p.val ∧ m ≤ Cash.numP p.val then ρ^p.val.card*∑ i:I', scalarWeight rA i * earnedBy p.val (Palette.team M' i) X k' else 0) Q.exp (swingTab Q L μ s ρ m y k'):=by
   subst k'
   have hh:= Coupons.collect S Q.halo c0 S' H.birth (Thermal.together M' rA X.flair) D T' he (hc.cards _ _ _ X.accrues) hρ hd (by norm_num : (1/2:ℝ)<1) 0 k m y
   intro i; convert! budget_pull (fun p:H.ThinP=>p.val) (Subtype.val_injective) (hh i) using 2; rename_i p
   dsimp only; split
   next h=>
     rw [if_pos (show i∈Finset.biUnion p.val (foot S Q.halo c0 H.birth) from h)]; apply congr_arg (·*_); rw [sumPower]; unfold Mixed.selected; by_cases h: y≤H.shapeW p.val ∧ m≤Cash.numP p.val; swap; · rw [if_neg h,if_neg (fun hp=>h ⟨hp.2.2.2,hp.2.2.1⟩),mul_zero]
     have hz : Allowed S Q.halo c0 S' H.birth D 0 m y p.val ↔ Allowed S Q.halo c0 S' H.birth D 0 0 0 p.val := by refine ⟨fun he=>⟨he.1,he.2.1,Nat.zero_le _,H.positive_volume _⟩,fun he=>⟨he.1,he.2.1,h.2,h.1⟩⟩
     simp_rw [if_pos h,hz]
   next h=> rw [if_neg (show i∉ Finset.biUnion p.val (foot S Q.halo c0 H.birth) from h)]

def entrances (Q:ConnectedActivityE6.Target G P)(L:Side)(μ s B ρ:ℝ)(k j M:ℕ):=
    let f m y:= swingTab Q L μ s ρ m y k
    (packets j M M*B)* (f 0 0+ρ^(M+1)*f 1 0 + ρ^(M+1)*f 0 (till s))
lemma income (h:WarnBudget Z N.conduit)(hv:1≤Z)(M:ℕ):
    Ac.Hit H.smallAt c0 (sumWeight N M' rA M ρ Z) Q.exp (entrances Q L μ s B ρ k j M):=by
   let K':=ρ^(M+1); let V i:= Palette.team M' (i:I'); let U:=pump h hv; let g (p:H.ThinP) i:= scalarWeight rA i * earnedBy p.val (V i) U k; let u p m y:= if y≤H.shapeW (p:H.ThinP).val ∧ m ≤ Cash.numP p.val then ρ^p.val.card*∑ i, g p i else 0
   have hh (p:H.ThinP): sumWeight N M' rA M ρ Z p=(packets j M M * B)*(u p 0 0+K'*u p 1 0+K'*u p 0 (till s)):=by
     unfold sumWeight reserveBy feeMix; let f i:=scalarWeight rA i * earnedBy p.val (V i) U k
     let t:=packets j M M * B * levyMix M p ρ*ρ^p.val.card
     have hu (i:I'): scalarWeight rA i*(packets j M M* B*(levyMix M p ρ*(Z^(blaze p.val).card)* (ρ^p.val.card*earnedBy p.val (V i) N.conduit k)))=t*f i:=by unfold t f U; rw [pumpMix]; ring
     change (∑ i,_)=_; rw [sum_congr rfl (fun i _=> hu i),← Finset.mul_sum]; unfold u; unfold g; rw [if_pos ⟨H.positive_volume _,Nat.zero_le _⟩]; unfold t levyMix K' f; simp only [H.positive_volume _,true_and,Nat.zero_le,and_true]; split_ifs <;> ring
   intro i; convert! budget_scale (mul_nonneg (zero_le_one.trans (package j M M)) N.balance) (budget_plus (budget_plus (existsHit (ρ:=ρ) M' rA U hc he hρ hd 0 k rfl 0 i) (budget_scale (pow_nonneg hρ.le (M+1)) (existsHit M' rA U hc he hρ hd 1 k rfl 0 i))) (budget_scale (pow_nonneg hρ.le (M+1)) (existsHit M' rA U hc he hρ hd 0 k rfl (till s) i))) using 2; rename_i p; rw [hh]; split
   next h=> ring
   next h=> ring
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
