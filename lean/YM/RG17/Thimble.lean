import YM.RG17.Rook
import YM.RG17.Temple
/-! Adapter next margin at ANY t -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G){S:Table R.family.book}{f: Extraction.Order}
 (fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
open Push
include R fx W
lemma stitches (t:ℕ): ∀ᶠ j in atTop,∀ {n:ℕ} {d:Fin n→ℕ} {r:ℝ} {N p:ℕ} {o:Fin n → Site (R.family.side (wheel R.family r) p)} {u:(i:Fin n)→ R.family.label (d i)} {e:ℝ}{k m:ℕ} {z:R.family.label t} (hr:Temple R d t r N p o u e k m z) (_:k≤ j) (hj:j ≤ m) (y:R.family.label t) (θ:ℝ),
     let P:= fun U=>liftVac R.family.path N p N U*(∏ i:Fin n,R.family.O N p (u i) (attachV R (wheel R.family r) (p:=p) o N i) U);
     (∀ x: Space G (0:Site (R.family.side j p)) (sizeQ R.family j), ‖x‖ ≤ (H j^6)⁻¹ →
          let U:=net (R.family.path.rep N p j).p 0 (sizeQ R.family j) x;
          ‖GridApprox.pushTo R.family.path N p (hj.trans hr.feeds) P U / liftVac R.family.path N p j U - awakeFull R.family j N p y U‖ ≤ θ) →
     paid R.family t j N p (z-y) ≤ H j^(3+6*t)*(θ+(1+((ι).params j).columns)*((e*R.family.S.a m^t)/(Bid.gainChart R.family.path m j)) / a j^t) :=by
    have ho:∀ᶠ k in atTop, ((ι).params k).columns ≤ H k := (eventually_ge_atTop 1).mono fun _ hk=> possibleOdds R fx W hk
    filter_upwards [paidThrough C t R.makes W.simpleGate ho,eventually_ge_atTop (C|>.ref t)] with j hv ht n d r N p o u e k m z hr hJ hj y θ P he
    have h':j ≤ N:=hj.trans hr.feeds
    apply (hv N p h').2
    obtain ⟨Z,hZ⟩:=hr.prime
    obtain ⟨⟨i,he',hz,hv'⟩,hE⟩:= hZ j hJ hj; intro x hx
    let U:=net (C|>.path.rep N p j).p 0 (sizeQ C j) x; have hU : flags (C|>.path.rep N p j).p.threshold U=∅:= (hv N p h').1 x hx
    let V:= GridApprox.pushTo R.family.path N p h' P U/liftVac R.family.path N p j U; let L w:= awakeFull C (d:=t) j N p w U
    have ha:L (z-y)=L z-L y:=by have hh:L (z+(-1:ℂ) • y)=L z + (-1)*L y:=(on_branch R.makes ht h' p U hU z).2.2 y (-1); simpa [sub_eq_add_neg] using hh
    change ‖L (z-y)‖≤_; rw [ha, add_comm]; refine le_trans (norm_sub_le_norm_sub_add_norm_sub (L z) V _) ?_; rw [norm_sub_rev (L z)]; exact add_le_add (spiresUp C N p j t R.makes (Z j) U z (GridApprox.pushTo R.family.path N p h' P) ht h' hE hU hz hv') (he x hx)
end YM.RG17
