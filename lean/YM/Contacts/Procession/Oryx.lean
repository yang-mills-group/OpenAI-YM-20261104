import YM.Contacts.Procession.Pulsar
noncomputable section
namespace YM.Contacts.Procession.Welcome.Theater
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide Barrage Slope House
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch
set_option autoImplicit false
variable {X Y A B ι κ α β: Type}{f m:Side} {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}
open Hinges Lotus
variable {Q M:TableFee} {σ η s:ℝ≥0}{g u:ℝ}{L:Side}
variable {T:Theater G} {B e:ℕ}
variable {F D:Field (Fin k) (Node (Dye G))}{x:Dye G}{z: Cover}
lemma float_pack [Fintype ι](F H:Field ι X)(a:ℝ)(p:X→Y)(hF:Summable F)(hH:Summable H): packing p (a • F+H)=a • packing p F+packing p H:= by have h: Scroll (hinge p) F (packing p F):=fun _=> rfl; have he: Scroll (hinge p) H (packing p H):= fun _=> rfl; exact funext fun i=> (((h.scale a).add he (hF.const_smul a) hH) i).symm
lemma path_tilt (T:Theater G) (ht:Summable F)(hp:Summable D)(a:ℝ)(z:Cover) : path T (a • F + D) z= a • path T F z+path T D z:= by
   have he (x:ℕ)(F:Field (Fin x) (Node (Dye G)))(hv:Summable F): T.path F z= packing (lane (Dye G) T.L ∘ backpack z) F:= pack_twice _ hv
   rw [he _ (a • F+D) ((ht.const_smul a).add hp), he _ _ ht,he _ _ hp,float_pack _ _ _ _ ht hp]
lemma spot_tilt (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val ≤ σ)(hs:Rest (terrain σ _) (0,x) F b)(hp:Poem F)(hc:Rest (terrain σ _) (0,x) D c)(hd:Poem D)(he:e<B)(hk:k≤B)(a:ℝ)(z:Cover): T.spot B e (a • F+D) z=a • T.spot B e F z+ T.spot B e D z:= by unfold Theater.spot; rw [path_tilt T hs.summ hc.summ]; exact (T.dome h).ray_tilt (path_cost hs ht (.inl x) z) (path_bless hp) he hk x (path_cost hc ht (.inl x) z) (path_bless hd) a
lemma empty_wick (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val≤σ)(he:e<B)(hk:k≤B)(x:Dye G)(z:Cover): T.spot B e (k:=k) 0 z=0:= by
   let F:= (0:Field (Fin k) (Node (Dye G))); let R:=T.spot B e F z; have hi : Rest (terrain σ _) (0,x) F 0:= Rest.zero; have hz:=spot_tilt h ht hi Poem.empty hi Poem.empty he hk 1 z; change R=0; apply add_left_cancel (a:=R); rw [add_zero]; simpa [F,R] using hz.symm
lemma spot_smul (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val≤σ)(hs:Rest (terrain σ _) (0,x) F b)(hp:Poem F)(he:e<B)(hk:k≤B)(a:ℝ)(z:Cover): T.spot B e (a • F) z=a • T.spot B e F z:= by
   simpa only [add_zero,empty_wick h ht he hk x z] using spot_tilt h ht hs hp (show Rest (terrain σ _) (0,x) (0:Field (Fin k) (Node (Dye G))) 0 from Rest.zero) Poem.empty he hk a z
/-- Price tied to an upper bound on *relabeled* primitive unit inputs across
all offsets. No need determine constants from diagram order afterwards.
-/
def gift (T:Theater G)(η:ℝ≥0)(g u c:ℝ)(Q:TableFee)(B e i:ℕ): ℝ:= (i+1:ℕ)* skies (Mixed G T.P) (Dye G) (T.wealth η Q) u g c (B+e) (i+1)
-- presentation terrestrial. Input payout key from coalesced budget.
lemma donates (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val≤σ)(hs:Rest (terrain σ _) (0,x) F b)(hc:stuff η σ z ≤ c)(hp:Poem F)(he:e<B)(hk:k≤B)(y:Dye G)(i:ℕ) : Rest (terrain η _) (0,y) (T.spot B e F z i) (gift T η g u c Q B e i*b):= by
   let X:= T.spot (k:=k) B e; by_cases hz:b=0
   swap
   ·
     let U:= b⁻¹ • F; let W:= path T U z; let V:= path_cost (hs.smul b⁻¹) ht (.inl x) z; have hb:b* b⁻¹=1:= mul_inv_cancel₀ hz; have hi:= hs.cash; have hh:Rest (terrain σ _) (0,x) U 1:= (hs.smul b⁻¹).ist (by rw [Real.norm_of_nonneg (inv_nonneg.mpr hi),inv_mul_cancel₀ hz]); have ht':= (path_cost hh ht (.inl x) z).ist (le_trans (mul_one (stuff η σ z)).le hc);
     have hr: Poem U:=hp.scale _; let v:= T.dome h; have hu: Rest (terrain η _) (0,y) (X U z i) (gift T η g u c Q B e i):= (reading_block (v.paidA 1) (e:=e) (j:=i) ht' v.Rfee v.beam v.hFee v.cbase y (v.warmed 1) he (path_bless hr) hk).room
     change Rest _ _ (X F z i) _; rw [show X F z=b • X U z from ?_, Pi.smul_apply]; · exact (hu.smul b).ist (le_of_eq (by rw [Real.norm_of_nonneg hi,mul_comm]))
     exact (spot_smul h ht hh hr he hk b z|>.symm.trans (show T.spot B e (b • U) z=X F z from (by unfold U; rw [smul_smul,hb,one_smul]))).symm
   rw [show F=0 from funext fun i=>norm_le_zero_iff.mp (by rw [hz] at hs; exact budget_single hs.raw i), empty_wick h ht he hk x, hz,mul_zero]; apply Rest.zero
end YM.Contacts.Procession.Welcome.Theater
