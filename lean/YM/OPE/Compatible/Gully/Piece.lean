import YM.OPE.Compatible.Gully.Sane
import YM.OPE.Compatible.Melon.Ritzy
/-!
# Path stamp read at one vertex. Matching connection
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
abbrev prairie (x:Bid.Dir G n):Stray G n:=fun i z=>x (addressR (z,i))
lemma entry (X:Bid.Dir G n)(v:Face (Per n)):faceValue (represent X) v=mace (layoutA (prairie X) v):=by
      let i:=v.2.val.1; let j:=v.2.val.2; unfold faceValue square; simp only [travel, Step.pos_read,Step.vec_pos,Step.neg_read,Step.vec_neg,mul_one]; rw [show v.1+step i+step j-step i=v.1+step j from by abel, show v.1+step i+step j+ -step i-step j=v.1 from by abel]; simp_rw [Work.F03.represent_link]; rw [mace]; change _*(_*(_*_))= _*_*_*_; unfold layoutA Nestle.localS
      rw [mul_assoc,mul_assoc]; rfl
lemma airyP(X:Bid.Dir G n)(v:Face (Per n))(t:ℝ): layoutA (prairie (t • X)) v=t • layoutA (prairie X) v:=by funext i;fin_cases i<;>rfl
lemma rise_w (X:Bid.Dir G n): iteratedDeriv 3 (fun t:ℝ=>Wilson.energy (represent (t • X))) 0=(G.colorScale^2*2)⁻¹*6*scribeX (prairie X) (prairie X) (prairie X):=by
    let g(v:Face (Per n))(x:ℝ):= G.price (mace (x • layoutA (prairie X) v)); have hv(v): ContDiffAt ℝ ω (g v) 0:=by
        let A:=layoutA (prairie X) v; have hp: ContDiff ℝ ω (fun t:ℝ=> maceX (t • A)):= satX A; have hb(x:ℝ): G.mat (mace (x • A))=maceX (x • A)+1:=by rw [maceX, sub_add_cancel]
        change ContDiffAt ℝ ω (fun x:ℝ=>G.price (mace (x • A))) 0; apply Work.F03.price_smooth; simp_rw [hb]; exact hp.contDiffAt.add contDiffAt_const
    simp only [Wilson.energy,entry,airyP]; erw [iteratedDeriv_fun_sum (I:=Finset.univ) (fun i _=> ((hv i).of_le le_top))]; unfold scribeX; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; unfold g hatB; rw [priceJet];ring
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{A:Alps B Q i l}
lemma launchEq : ContDiffAt ℝ ω (Wilson.energy ∘ (represent (G:=G) (n:=n))) 0:=by
     unfold Wilson.energy; apply ContDiffAt.sum; intro a _; apply Work.F03.price_smooth; -- show by entry.composition.F smooth
     let L(y:Bid.Dir G n):=layoutA (prairie y) a; have he:ContDiff ℝ ω L:=by refine contDiff_pi.mpr fun i=>?_ ; fin_cases i <;> exact contDiff_pi.mp (show ContDiff ℝ ω (fun v:Bid.Dir G n=>v) from contDiff_id) _
     simp_rw [entry,show ∀ (X: Stubble.Tile G),G.mat (mace X)= maceX X+1 from fun i=>by rw [maceX, sub_add_cancel]]; exact (sheet.comp he).contDiffAt.add contDiffAt_const
variable {H:Even n.val}
def Track (A:Alps B Q i l) (n:Side):Prop :=iteratedFDeriv ℝ 3 (frameD A (n:=n)) 0=iteratedFDeriv ℝ 3 (Wilson.energy ∘ represent) 0 -- lint
lemma dataX (X:Keys G (Limb H))(hs:Track A n): jet (mural H A) 3 X=(G.colorScale^2*8)⁻¹ * scribeX (exclaim H X) (exclaim H X) (exclaim H X):=by
      let L:=cloak H (G:=G); let f:=frameD A (n:=n); have he:ContDiffAt ℝ ω f 0:=(A.fullK 1).plot n; have ht:ContDiffAt ℝ ((↑(3:ℕ)):WithTop ℕ∞) (f ∘ L) 0:= ((L.map_zero.symm ▸ he : ContDiffAt ℝ ω f _).comp _ L.contDiff.contDiffAt).of_le le_top
      have hv:mural H A=(4:ℝ)⁻¹ • (f ∘ L):=funext fun i=>by change (f ∘ L) i/4= 4⁻¹*((f ∘ L) i);ring -- not def
      unfold jet; erw [hv,iteratedFDeriv_const_smul_apply ht,jets_linear L (he.of_le le_top), show iteratedFDeriv ℝ 3 f 0=_ from hs]; let T:=L X
      change _⁻¹*(4⁻¹*Tensor.diagonal (iteratedFDeriv ℝ 3 (Wilson.energy ∘ represent) 0) T)= _; rw [← iteratedDeriv_on_line ((launchEq (n:=n)).of_le le_top) (T)]; erw [rise_w]; change ((3:ℕ).factorial:ℝ)⁻¹*(4⁻¹*((G.colorScale^2*2)⁻¹*_ * scribeX (prairie T) (prairie T) (prairie T)))=(G.colorScale^2*8)⁻¹ * scribeX (prairie T) (prairie T) (prairie T); norm_num [Nat.factorial_succ]; ring
end YM.OPE.StageLight
