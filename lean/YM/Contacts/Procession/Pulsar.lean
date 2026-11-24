import YM.Contacts.Procession.Bay
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
variable (T:Theater G)(B e:ℕ)
abbrev path (F:Field (Fin k) (Node (Dye G)))(z:Cover) : Field (Fin k) (Node (Mixed G T.P)):= packing (lane (Dye G) T.L) (packing (backpack z) F)
abbrev spot (F:Field (Fin k) (Node (Dye G)))(z:Cover) := ray T.belt T.spout T.seas B e (path T F z)
abbrev scouts (F:Field (Fin k) (Node (Dye G)))(z:Cover)(m:Side):= peer T.belt T.spout T.ceiling e (path T F z) m
variable {T B e} {F D:Field (Fin k) (Node (Dye G))}{x:Dye G}{Y:Mixed G T.P}{z: Cover}
def stuff (η s:ℝ≥0)(z:Cover) := Real.exp (4*η:ℝ)*parcelY s z
lemma path_cost (h: Rest (terrain σ _) (0,x) F b) (ht:(η:ℝ)/↑T.L.val≤σ) (v:Mixed G T.P) (z:Cover): Rest (terrain η _) (0,v) (T.path F z) (stuff η σ z*b):= by
   rw [stuff,mul_assoc]; refine pack_cost (lane (Dye G) T.L) (lane_inj _ _) (staple z h) (Real.exp_pos _).le (fun u'=> lane_strip u' x v ht)
lemma path_bless (hp:Poem F): Poem (T.path F z) := poetic _ (poetic _ hp _) _
lemma plan_seek (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val ≤ σ)(hs: Rest (terrain σ _) (0,x) F b)(hp: Poem F)(hi:e<B)(hb:k ≤ B)(y:Dye G)(m:Side)(z:Cover)(i:ℕ): Alive η ((i+1:ℕ)* skies (Mixed G T.P) (Dye G) (T.wealth η Q) u g (stuff η σ z*b) (B+e) (i+1)) ((i+1:ℕ)*(hush η m* stalks (Mixed G T.P) (Dye G) (T.wealth η Q) u g (stuff η σ z*b) (B+e) (i+1))) y (spot T B e F z i) m (scouts T e F z m i):= by
    let H:= T.dome h; exact reading_block (H.paidA m) (path_cost hs ht (.inl x) z) H.Rfee H.beam H.hFee H.cbase y (H.warmed _) hi (path_bless hp) hb
lemma horizon_approach (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val ≤ σ)(hs: Rest (terrain σ _) (0,x) F b)(hp:Poem F)(hi:e<B)(hb:k≤B)(z:Cover)(j:ℕ)(v:Fin j→ Node (Dye G)) (A:ℕ→ Side)(hm:Tendsto (fun i=>(A i).val) atTop atTop): Tendsto (fun i=> scouts T e F z (A i) j (lower (A i) ∘ v)) atTop (𝓝 (spot T B e F z j v)):= (dome T h).river (path_cost hs ht (.inl x) z) (path_bless hp) hi hb x hm v
lemma pure_parade (h: T.Rich s η g u Q) (ht:(η:ℝ)/↑T.L.val ≤ σ)(hs:Rest (terrain σ _) (0,x) F b)(hp:Poem F)(he:k ≤ B)(hb:0<B) (z: Cover): spot T B 0 F z k= printRun (Trace.wreath z (install (Origin.stretch T.P T.K G T.W.V)) F) := by
   let L:= T.L; let R:= Origin.stretch T.P T.K G T.W.V; let K:=packing (backpack z) F; have hK:Poem K:= poetic _ hp _; have hh:Row.strip R η u:= fun i=> by exact fun j=> h.scope (Sum.inr i) j -- elaborates
   have ht':=staple z hs; have hk: Summable (lifts R K):=(hoist_price x hh (zero_le_one.trans h.hold) ht ht').summ; have hx:= T.dome h; have hv(m:Side): scouts T 0 F z m k=packing (lower m) (lifts R K):= by
      let A:= T.Ut m; let S:= A.ratio; let P:= packing (lower m) (path T F z); let H:= installed S R; let J:=pack_hoist (F:=K) S hh x (zero_le_one.trans h.hold) ht ht'; have hw: scouts T 0 F z m k= hoist (T.spout.acts m) P:= by
           change hoist _ (canal _ k _ (leafS P) 0 k)=_; rw [pure_row _ (hx.warmed m) _ (bornS _ (poetic _ (path_bless hp) _))]; simp [leafS,P]; -- congr R proof
      let Q:= packing (lower (m*T.P.L)) K; have Hh: P=hoist (shave A G) Q:= Welcome.advance (S:=A) K hK ht'.summ
      suffices H₁: hoist (T.spout.acts m) P= hoist H Q by exact hw.trans (H₁.trans J.symm)
      apply design_eq hoist_shape hoist_shape; funext y; let X':= H*ᵥ y; let v:=T.spout.acts m *ᵥ y
      calc
         _= design P v:=hoist_read ..
         _= design Q (shave A G *ᵥ v):= (congr_arg (fun x'=> design x' v) Hh).trans (hoist_read ..)
         _= design Q X':= by apply congr_arg; rw [shaved]; unfold v; rw [show T.spout.acts m= Forge.sky A G H from skytop A R]; exact (congr_arg (teen A) (sky_pass ..)).trans (Spark.blooms (S:=A) (y,H *ᵥ y))
         _= _:= (hoist_read ..).symm
   rw [orchid]; funext v; apply tendsto_nhds_unique (horizon_approach h ht hs hp hb he z k v _ stepping); simp_rw [hv]; exact portraying v hk stepping
lemma dropping (h:T.Rich s η g u Q)(ht:(η:ℝ)/↑T.L.val ≤ σ)(hs: Rest (terrain σ _) (0,x) F b)(hp:Poem F)(hi:e<B)(hb:k≤B)(hx:k+e<r)(z:Cover): spot T B e F z r=0:= by
    have he (m:Side): T.scouts e F z m r=0:= (rose_shape (T.dome h|>.warmed m) (poetic _ (path_bless hp) _)).thin _ _ hx; funext v; apply tendsto_nhds_unique (horizon_approach h ht hs hp hi hb z r v _ stepping); simp_rw [he]; exact tendsto_const_nhds
lemma plow_offset (p i r:ℕ) (T:Theater G)(X:bore G)(z:Cover): T.plow p (migrated X z) i r= ∑ j ∈Finset.range (i+1),∑ k∈Finset.range (p+j+1),T.spot (dart i k) (i-j) (X j k) z r:= by simp_rw [plow,hearthC,Finset.sum_apply]; rfl
end YM.Contacts.Procession.Welcome.Theater
