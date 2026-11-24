import YM.RegulatorIR.Binding.Landscape

/-! Iteration of parameter readers. Assemble a *single compact gauge
chamber* of all previously opened fibers = independent integrating spins.
Zero-order gap on pure X proven rather than assumed for this product
chamber. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {I J E L:Type}[Fintype E][Fintype I][Fintype J][Fintype L]
variable {F:Hook G E I}{Z:Hook G L J}{V:Transfer I L G}{P:Viewport G I}{Q:Viewport G J}

def beanK (E L:Type)(G:Gauge): RoomK G (E⊕L)≃ᵐ RoomK G E × RoomK G L:= MeasurableEquiv.sumPiEquivProdPi (fun _=> G.El)
def trestle (u: RoomK G (E⊕L)):= beanK E L G u
omit [Fintype E][Fintype L] in
lemma trestle_cont : Continuous (trestle (G:=G) (E:=E) (L:=L)) := by
 apply Continuous.prodMk <;> apply continuous_pi
 all_goals intro i; change Continuous (fun u:RoomK G (E⊕L)=>u _) ; exact continuous_apply _

def dart (E L:Type)(G:Gauge): Meadow G (E⊕L)≃ₗ[ℝ] Meadow G E × Meadow G L where
 toEquiv:=Equiv.sumPiEquivProdPi _
 map_add' _ _:=rfl
 map_smul' _ _:=rfl

abbrev Angle (E I:Type)(G:Gauge):= Meadow G E × ℝ × Meadow G I

def drawUp (V:Transfer I L G): Angle (E⊕L) J G →ₗ[ℝ] Angle E I G where
 toFun x := let z:=dart E L G x.1; (z.1,x.2.1,V.curve z.2)
 map_add' _ _:=Prod.ext rfl (Prod.ext rfl (V.curve.map_add ..))
 map_smul' _ _ :=Prod.ext rfl (Prod.ext rfl (V.curve.map_smul ..))


def front (J L E:Type) (G:Gauge) : Angle (E⊕L) J G →ₗ[ℝ] Angle L J G where
 toFun x:=((dart E L G x.1).2,x.2)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl

def blade (J:Type)(V: Transfer I L G)(A:Hook G E I) : Hook G (E⊕L) J:= fun t _ u => A t (V.inlet (trestle u).2) (trestle u).1
def fuse (V:Transfer I L G)(F:Hook G E I)(Z:Hook G L J) : Hook G (E⊕L) J:= fun t y x=> blade J V F t y x + Z t y (trestle x).2
omit [Fintype E][Fintype I][Fintype J][Fintype L] in
lemma blade_map (x:Angle (E⊕L) J G) : priceMap (blade _ V F) x= priceMap F (drawUp V x):=by
 change _=F _ (expLinks G _ (V.curve (dart E L G x.1).2)) _; rw [← V.invariant]; rfl
lemma blade_c (J:Type)[Fintype J] {A:Hook G E I} (h:Tune A) : Tune (blade J V A) := by
 constructor
 · let g (u:ℝ × RoomK G J × RoomK G (E⊕L)):= (u.1,V.inlet (trestle u.2.2).2,(trestle u.2.2).1)
   exact Continuous.comp h.view (show Continuous g from continuous_fst.prodMk ((V.continuous.comp (continuous_snd.comp (trestle_cont.comp (continuous_snd.comp continuous_snd)))).prodMk (continuous_fst.comp (trestle_cont.comp (continuous_snd.comp continuous_snd)))))
 rw [show priceMap _=priceMap A ∘ drawUp V from funext fun x=>blade_map x]
 let p:= drawUp (J:=J) (E:=E) V; have ht : p 0=0:= p.map_zero
 apply (ht.symm ▸ h.smooth).comp 0 (show ContDiffAt ℝ ∞ p 0 from p.toContinuousLinearMap.contDiff.contDiffAt)

variable (H:Stead P F)(N: Move P Q V Z)
namespace Stead

include H N
lemma fused_S : Stationary (priceMap (fuse V F Z)) ∧ ∀ x: Angle (E⊕L) J G, jet (priceMap (fuse V F Z)) 2 x=
    jet (priceMap F) 2 (drawUp V x)+jet (priceMap Z) 2 (front J L E G x):=by
 let p: Angle (E⊕L) J G →ₗ[ℝ] Angle E I G := drawUp V; let q:= front J L E G
 let f:= priceMap F; let n:= priceMap Z; let g:=priceMap (fuse V F Z)
 have he(x): g x=f (p x)+n (q x):= congr_arg (fun v=>v+n (q x)) (blade_map x)
 have hx x: Tendsto (fees g · x) (𝓝[≠] 0) (𝓝 (jet f 2 (p x) +jet n 2 (q x))):= by
    convert Tendsto.add (due _ H.localK (p x)) (due _ N.localK (q x)) using 1
    ext1 t; change g _/ _= f _/ _+n _/ _
    rw [he (t • x), map_smul, map_smul,add_div]
 have h: Stationary g:=by
    apply declares _ _ (fun x=> ⟨_,hx x⟩)
    rw [funext he]; refine ((show ContDiffAt ℝ ∞ f (p 0) by rw [map_zero]; exact H.localK.smooth).comp (f:=p) _ p.toContinuousLinearMap.contDiff.contDiffAt).add ((show ContDiffAt ℝ ∞ n (q 0) by rw [map_zero]; exact N.localK.smooth).comp (f:=q) _ q.toContinuousLinearMap.contDiff.contDiffAt)
 exact ⟨h,fun x=>tendsto_nhds_unique (due g h x) (hx x)⟩
lemma fuse_where (r :ℕ→ℝ)(x:ℕ→ RoomK G J)(u:ℕ→ RoomK G (E⊕L)) (X W) (hr:Tendsto r atTop (𝓝 0)) (hx:Tendsto x atTop (𝓝 X)) (hu:Tendsto u atTop (𝓝 W))(he:Tendsto (fun i=> fuse V F Z (r i) (x i) (u i)) atTop (𝓝 0)): Q.room X ∧ (X=1→ W=1):=by
 let p i := F (r i) (V.inlet (trestle (u i)).2) (trestle (u i)).1; let q i:= Z (r i) (x i) (trestle (u i)).2
 let v := trestle W
 have hp:Tendsto p atTop (𝓝 0) := squeeze_zero (fun _=> H.nonneg ..) (fun i=>le_add_of_nonneg_right (show 0 ≤ q i from N.nonneg ..)) he
 have hh:Tendsto q atTop (𝓝 0):=squeeze_zero (fun _=> N.nonneg ..) (fun i=>le_add_of_nonneg_left (show 0≤p i from H.nonneg ..)) he
 have Hf:= ((trestle_cont (G:=G) (E:=E) (L:=L)).tendsto W).comp hu
 obtain ⟨hA,hB⟩:= H.whereR r _ _ (V.inlet v.2) v.1 hr ((V.continuous.tendsto _).comp ((continuous_snd.tendsto v).comp Hf)) ((continuous_fst.tendsto v).comp Hf) hp
 obtain ⟨hQ,hD⟩:= N.whereS r _ _ _ v.2 hr hx ((continuous_snd.tendsto v).comp Hf) hh hA
 refine ⟨hQ,fun hk=> (beanK E L G).injective (Prod.ext (hB ?_) (hD hk))⟩
 rw [hD hk,← expOrigin L, V.invariant, map_zero,expOrigin]
lemma integrates : Stead Q (fuse V F Z):=by
 obtain ⟨h,hz⟩:= fused_S H N
 refine ⟨?_,fun t x y=>add_nonneg (H.nonneg ..) (N.nonneg ..),h,fuse_where H N,?_⟩
 · let g (u:ℝ × RoomK G J × RoomK G (E⊕L)):= (u.1,V.inlet (trestle u.2.2).2,(trestle u.2.2).1)
   let w (u:ℝ × RoomK G J × RoomK G (E⊕L)):= (u.1, u.2.1,(trestle u.2.2).2)
   have ht:Measurable (trestle (E:=E) (L:=L) (G:=G)):=trestle_cont.measurable
   have he:Measurable g:=measurable_fst.prodMk ((V.continuous.measurable.comp (measurable_snd.comp (ht.comp (measurable_snd.comp measurable_snd)))).prodMk (measurable_fst.comp (ht.comp (measurable_snd.comp measurable_snd))))
   exact (H.seen.comp he).add (N.seen.comp (show Measurable w from measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp (ht.comp (measurable_snd.comp measurable_snd))))))
 intro z; rw [hz]; obtain ⟨ht,hx⟩:= H.scope (drawUp V z); obtain ⟨hm,hQ⟩:= N.sphere (front J L E G z); refine ⟨add_nonneg ht hm,fun he=>?_⟩
 obtain ⟨h₁,h₂⟩:=hx (by linarith); obtain ⟨h₃,h₄⟩:= hQ (by linarith) h₁; refine ⟨h₃,fun hb=> (dart E L G).injective (Prod.ext (h₂ ?_) (h₄ hb))⟩
 change V.curve ((front J L E G z).1) =0
 rw [h₄ hb, map_zero]
end Stead
end YM.RegulatorIR.Binding
