import YM.LocalLTE.Port.Lumps
/-! # Prices under finite marker aggregation. Units separate. Override regular/pure projection via actual powers step prices.
Retained markers and named seats all. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories
variable [Fintype J]
-- menu.BK.All permit log and Leaf.Edition modules.Sc.WeightZERO unit.
structure PL (o:V→Site f)(M:I→Menu.Hat R Q): Prop where
    mark i: originQ R o (M i)
    segment: ∀ i,∃ k,(M i).M.turn=.logKey k
    ID : ∀ i j k,(M i).M.turn=.logKey k→(M j).M.turn=.logKey k→ i=j
-- price output.Identity projection.Z.Shutter values served via Leaf.Cost.Array units
section
variable {P:V→ℝ}(X: J→ RegularAddress f)(K:J→ R.Mode)(u:J→ℝ)(hX:∀ i,(K i).val.Nonempty∧ (K i).val.image o⊆ (X i).support) (φ:J→ Bool→ Config G f→ℝ)(hP:∀ i k,Sale Q.p (X i).support (φ i k) (u i)) (hm:HasSlots Q.p Q.activities)
variable (e:J×Bool↪ℕ)
-- uses φ∞ for both multipliers assignments.YM.
def lea (i:J×Bool) := salesZ Q R (X i.1) (e i) (φ i.1 i.2) (K i.1) (hX i.1|>.1) (u i.1) (ink i.2) (hP i.1 i.2) hm
local notation "W"=> lea o X K u hX φ hP hm e
omit [Fintype V] [Fintype J] in
lemma joinsL : PL o (W) :=by
    constructor
    · rintro ⟨i,k⟩; let h:= birthZ Q R (X i) (e (i,k)) _ (K i) (hX i|>.1) _ k (fun _=>0) (hP i k) hm; unfold originQ; rw [show ((W) (i,k)).M.crest = _ from h.2.1]; exact (hX i).2
    · intro i; exact ⟨_,rfl⟩
    intro i j k hi hj
    have hx : blankRow f (X i.1,e i)=blankRow f (X j.1,e j):= Wing.logKey.inj (hi.trans hj.symm); exact e.injective (congr_arg Prod.snd ((blankRow f).injective hx))
variable [Countable I] (I':I→J)(Y:I→ Config G f→ℂ)
omit [Fintype V] [Fintype J] in
lemma rend (i:J)(k:Bool) : (W (i,k)).M.turn=.logKey (blankRow f (X i,e (i,k))):=rfl
-- carrier.Poly actor.Temporal r bound needs total. avoid multiplying cost by number Prim.Engine.Size only duplicated.
variable {b:ℝ} (x:J→ℝ)
omit [Fintype V] in
lemma prices (h:∀ i, u i=x i) : (∑ i:J×Bool, sumFee (W i) r * Q.p.mass (W i).M.crest (W i).M.weight)= 2*∑ i: J, Poly.toll r (K i)* Q.p.mass (X i).support (x i):=by
    rw [Fintype.sum_prod_type,mul_sum]; apply Finset.sum_congr rfl; intro i _
    have hk(k:Bool):sumFee (W (i,k)) r * Q.p.mass (W (i,k)).M.crest (W (i,k)).M.weight = Poly.toll r (K i)* Q.p.mass (X i).support (x i):=by
       rw [← h]; let Z:=birthZ Q R (X i) (e (i,k)) (φ i k) (K i) (hX i|>.1) (u i) k r (hP i k) hm; rw [show (W (i,k)).M.crest = (X i).support from Z.2.1, show sumFee (W (i,k)) r= _ from Z.2.2.2.2.1]; rfl
    rw [Fintype.sum_bool,hk,hk]; ring

-- C.mixed.AF.MUL.Pay.Sum decomposition.Exponent. Factor fields already masked.
variable (hy:∀ V,Summable (fun i=>Y i V))
    (hp:∀ k p V, (φ k p V)= scaleQ p (cram I' (fun i=>Y i V) k))
include hp hy
omit [Fintype V] [Countable I] in
lemma mother (z0:Config G f): Menu.roll W z0 = ∑' i, Marker.Poly.send (K (I' i)) (Y i z0):=by
    let b i:=(K (I' i)); let y (i:I):=Y i z0; let s:= cram I' y; let f (i:I):= Marker.Poly.send (b i) (y i)
    have hx(k:J): HasSum (fun i:{i//I' i=k}=> f i.val) (Poly.send (K k) (s k)):=by
        let Q:ℂ →L[ℂ] Poly R:= { toFun := Poly.send (K k),
                                 map_add' := fun x y=> by
                                      ext i; simp; split <;> ring
                                 map_smul' := fun x y=> (Menu.sent _ _ _).symm
                                 cont:= Overlay.Bands.sends _ } -- parser
        refine (Q.hasSum ((hy z0|>.comp_injective (show Injective (Subtype.val : {i//I' i=k}→I) from Subtype.val_injective)).hasSum)).congr_fun fun i=> ?_; unfold f b; rw [i.property]; rfl
    have he: Summable f:= by
       let w:= fun _: V => (1:ℝ) -- z0 shadow fix
       have ht:Summable (fun i=>Poly.price w (f i)):=by simp [w,f,Poly.toll]; exact (hy z0).norm
       exact (Poly.budgeted (w:=w) (fun _=>zero_lt_one) ht (fun _=>le_rfl)).1
    change _=∑' i,f i; rw [Port.rollCall _ _ z0 (Port.joinsL o X K u hX φ hP hm e).segment,Fintype.sum_prod_type];
    have hu: ∑ j:J, Marker.Poly.send (K j) (s j)=∑' i,f i:=by rw [← tsum_fintype (L:=SummationFilter.unconditional _),← (he.hasSum.tsum_fiberwise I').tsum_eq]; exact tsum_congr (fun i=> (hx i).tsum_eq.symm)
    rw [← hu]; apply Finset.sum_congr rfl; intro i _
    have hl(p): amount (W (i,p)) z0= Poly.send (K i) ((↑(scaleQ p (s i)):ℂ)* ink p):=by
       rw [← show φ i p z0 = scaleQ p (s i) from hp .. ]; exact Menu.varnish ..
    simp_rw [hl]; ext p; rw [Poly.part_sum]; simp_rw [Poly.part_send]; split; next h=>exact harvestQ _
    next hx=> simp only [Finset.sum_const_zero]
end
end YM.LocalLTE.Port
