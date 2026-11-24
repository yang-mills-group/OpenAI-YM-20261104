import YM.Contacts.Barrage.Cheque
import YM.Contacts.Milling.Choice
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{s η:ℝ≥0}{b c e:ℝ}{P: Patch}{B H:Bed}{m f L : Side}{n r k i j:ℕ}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
variable (T:MapPrices) (G)
variable (P : Patch)(K: KernelChoices)(Q: ChartRatio G)
def lush (x:ℝ):ℝ :=2+max 0 (Real.log (Real.log x))
lemma lush_matures : Tendsto lush atTop atTop:= (tendsto_atTop_add_const_left _ 2 (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).congr' (by filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0] with x hx; exact congr_arg (2+·) (max_eq_right hx).symm)
lemma lush_pos (x:ℝ) : 0 < lush x:= by unfold lush; linarith only [le_max_left 0 (Real.log (Real.log x))]
lemma lush_one (x:ℝ) : 1 ≤ lush x:= by unfold lush; linarith only [le_max_left 0 (Real.log (Real.log x))]
def narrow (x:ℝ): ℝ≥0:=⟨(lush x)⁻¹,(inv_pos.mpr (lush_pos x)).le⟩
lemma narrow_pos (x:ℝ):0<narrow x:=inv_pos.mpr (lush_pos x)
structure Wealth (Q:ChartRatio G) (y:ℝ) (H:ℕ) :Prop where
  escape : ∃ t:ℝ≥0,∃ b:ℝ, 0<t∧t≤ gate T P.J ∧ 1 ≤ b ∧ b ≤ lush y ∧ 2 * narrow y ≤ t ∧ (P.Branches K G →∀ B:Bed,B.metric.strip (T.α P.J) (purse T P.J) → (∀ n,(B.metric.acts n)ᵀ=B.metric.acts n ∧ Gap (B.metric.acts n) (T.η P.J)) → ∀ V:Wheel G P K B,Span G T P K P.J t b B V)
  length : P.L.val ≤ lush y
  shelf : spanned P (rentCheque T P.J) (purse T P.J) ≤ lush y
  need i (hi: i ≤ P.J) : purse T i ≤ lush y ∧ (kin_bill T i).choose ≤ lush y
  preState i (hi:i ≤ P.J) j (he:j≤ H): share T G i j ≤ lush y
  bud : (Fintype.card (Co P.L (Dye G)):ℝ) ≤ lush y ∧ (Fintype.card (Co P.L (Candles G)):ℝ) ≤ lush y ∧ (Fintype.card (Mixed G P):ℝ) ≤ lush y
  oil i (he:i≤ H) : Rooted (terrain 1 _) (Spark.sparkles P Q i) (lush y) ∧ Rooted (terrain 1 _) (fireworks P K G i) (lush y) ∧ |loaded 1 Q P K 0 i 0| ≤ lush y -- loaded monotone upper used later
  iron : 2 ≤ y ∧ G.slopeConstant*Real.log P.L.val ≤ y
lemma promised (n : ℕ) : ∀ᶠ i in atTop, Wealth G T P K Q i n := by
   obtain ⟨t,v,ht,hv,hh,H⟩:= wheel_bank G T P K P.J; have hu : ∀ i≤ P.J,∀ᶠ y in atTop,purse T i ≤ lush y ∧ (kin_bill T i).choose ≤ lush y ∧ ∀ j≤n, share T G i j≤lush y:= by
      intro i _; exact (lush_matures.eventually_ge_atTop _).and ((lush_matures.eventually_ge_atTop _).and ( ( (eventually_all_finset (Finset.Iic n) (p:=fun j y=> share T G i j ≤ lush y)).mpr (fun j _=> lush_matures.eventually_ge_atTop _)).mono fun y h j hj=> h j (Finset.mem_Iic.mpr hj)))
   have he : ∀ j∈ Finset.Iic n,∀ᶠ y in atTop, Rooted (terrain 1 _) (Spark.sparkles P Q j) (lush y) ∧ Rooted (terrain 1 _) (fireworks P K G j) (lush y) ∧ |loaded 1 Q P K 0 j 0| ≤ lush y:= fun j _=> (((lush_matures.eventually_ge_atTop _).mono fun y h=> (aboard_summed (Spark.templates G P) 1 _).weaken (fun _=>le_rfl) h).and (((lush_matures.eventually_ge_atTop _).mono fun y h=>(aboard_summed _ 1 _).weaken (fun _=>le_rfl) h).and (lush_matures.eventually_ge_atTop _)))
   filter_upwards [lush_matures.eventually_ge_atTop v, lush_matures.eventually_ge_atTop (2/(t:ℝ)), lush_matures.eventually_ge_atTop (P.L.val:ℝ), lush_matures.eventually_ge_atTop (spanned P _ (purse T P.J)), (eventually_all_finset _).mpr he, (eventually_all_finset (Finset.Iic P.J)).mpr (fun i hi=> hu i (Finset.mem_Iic.mp hi)), lush_matures.eventually_ge_atTop (Fintype.card (Co P.L (Dye G)):ℝ),lush_matures.eventually_ge_atTop (Fintype.card (Co P.L (Candles G)):ℝ),lush_matures.eventually_ge_atTop (Fintype.card (Mixed G P):ℝ), ((eventually_ge_atTop 2).and (eventually_ge_atTop (G.slopeConstant*Real.log P.L.val)))] with y h ht1 hL hs hE hp hv1 hv2 hv3 hR
   refine ⟨⟨t,v,ht,hv,hh,h,?_,H⟩,hL,hs,fun i hi=> ⟨(hp i (by simpa)).1,(hp i (by simpa)).2.1⟩,fun i hi j hj=>(hp i (by simpa)).2.2 j hj,⟨hv1,hv2,hv3⟩, fun j hj=> hE j (by simpa),hR⟩; apply NNReal.coe_le_coe.mp; push_cast; change 2*(lush y)⁻¹≤(t:ℝ); rw [← div_eq_mul_inv,div_le_iff₀ (lush_pos y)]; exact le_trans ((div_le_iff₀ (NNReal.coe_pos.mpr ht)).1 ht1) (mul_comm ..).le
open Org PhysicalNext.Repeat.Legato
variable {G} {A:Levels G}
def fee (L:Side)(j:ℕ) :ℝ:= if h:∃ P:Patch,P.L=L ∧ P.J=j then (eventually_atTop.mp (promised G T h.choose K Q j)).choose else 0
lemma fee_spend (L:Side)(K:KernelChoices)(j:ℕ) (P:Patch)(h:P.L=L ∧ P.J=j) (x:ℝ) (he:fee T K Q L j ≤ x): Wealth G T P K Q x j:= by
   let w:∃ P:Patch,P.L=L∧P.J=j:=⟨P,h⟩; rw [fee,dif_pos w] at he; have ht:P=w.choose:= by exact (fun (q : Patch) (hh:q.L=L ∧ q.J=j)=>by apply (show ∀ (P Q:Patch), P.J=Q.J→P.L=Q.L→P=Q from by rintro ⟨L,i,_⟩ ⟨p,q,_⟩ h h'; cases h; cases h'; rfl) P q (h.2.trans hh.2.symm) (h.1.trans hh.1.symm) : ∀ q:Patch,(q.L=L∧q.J=j) → P=q) w.choose w.choose_spec
   rw [ht]; exact (eventually_atTop.mp (promised G T w.choose K Q j)).choose_spec x he
def tint (T:MapPrices) (j:ℕ):ℕ:= Nat.ceil ((sight T (j-1):ℝ)/(sight T j:ℝ))
structure Mirage (T:MapPrices)(a:Levels G)(Q:ChartRatio G):Prop where
    funds (i:ℕ): planned T G (a.clock.J (i+1)) ≤ (mainFlag a i).L.val
    halo (i:ℕ): tint T (a.clock.J (i+1)) ≤ (mainFlag a i).L.val
    owns i : Wealth G T (mainFlag a i) a.clock.kernel Q (a.clock.hatBeta i) (a.clock.J (i+1))
    here : Truce T a

def bonus (t:BidTri G) : BidTri G:= ⟨fun K i=>max (t.w K i) (max (planned K G i) (tint K i)), fun U p i=> max (t.pay U p i) (fee U.K U.p.kernel U.O (p i) i)⟩
lemma grants {t:BidTri G}{p:Passage G}(h:admits (bonus t) p): admits t p ∧ Mirage p.M.K p.A.B.a p.M.O:= by
   refine ⟨fun i=> ⟨(le_max_left ..).trans (h i).1,(le_max_left ..).trans (h i).2⟩,(fun i=>  ((le_max_left ..).trans ((le_max_right ..).trans (h i).1))), (fun i=> (le_max_right ..).trans ((le_max_right ..).trans (h i).1)),fun i=>?_,p.peace⟩; let j:=(p.A.B.a.clock.J (i+1)); apply fee_spend p.M.K p.M.O (p.L.L j) -- args?
   · exact ⟨(p.A.B.a.fits.sameFactor i).symm.trans (congr_fun p.A.B.valid.lengths _), rfl⟩
   exact ( (congr_arg (fun k=>fee p.M.K k p.M.O (p.L.L j) j) p.A.B.valid.kernel).le.trans ( (le_max_right ..).trans (h i).2))
end Reserve
end
end YM.Contacts.Barrage
