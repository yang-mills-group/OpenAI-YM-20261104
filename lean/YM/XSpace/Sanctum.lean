import YM.XSpace.Camellia
/-!
# Leaf decay through the cubic
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Gland Chart2 Octave Season Lattice MvPolynomial Chiral Graph3 Player Relief Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{W: Initialize G}{ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{c:Shade.Cut}{u v b:E4}
variable (t:Captain c L a x y z u v b)
-- real calculation in each radial scene. Move translated Survey.Goods.
variable {A B C A' B' C':Toe}
local notation "₹"=> Sail.cover
private lemma ret_sub (ha:A∈Terrain 4)(ha':A'∈Terrain 4)(hb:B∈Terrain 3)(hc:C∈Terrain 3)(x y z:Cover):
 Trail x y z (A-A') B C= Trail x y z A B C-Trail x y z A' B C:=by unfold Trail Form; simp_rw [Pi.sub_apply,sub_mul]; exact (form_sum ha hb hc (by norm_num) x y z).tsum_sub (form_sum ha' hb hc (by norm_num) x y z)
private lemma ret_left {A B B' C:Toe}(ha:A∈Terrain 4)(hb:B∈Terrain 3)(hb':B'∈Terrain 3)(hc:C∈Terrain 3)(x y z:Cover):
 Trail x y z A (B-B') C=Trail x y z A B C-Trail x y z A B' C:=by unfold Trail Form; simp_rw [Pi.sub_apply,mul_sub,sub_mul]; exact (form_sum ha hb hc (by norm_num) x y z).tsum_sub (form_sum ha hb' hc (by norm_num) x y z)
private lemma ret_right (ha:A∈Terrain 4)(hb:B∈Terrain 3)(hc:C∈Terrain 3)(hc':C'∈Terrain 3)(x y z:Cover):
 Trail x y z A B (C-C')=Trail x y z A B C-Trail x y z A B C':=by unfold Trail Form; simp_rw [Pi.sub_apply,mul_sub]; exact (form_sum ha hb hc (by norm_num) x y z).tsum_sub (form_sum ha hb hc' (by norm_num) x y z)
private abbrev seqT (x y z:ι→Cover)(A B C:Toe):= fun i:ι=>Trail (x i) (y i) (z i) A B C
include t in
lemma burnt_a (ha:A∈Terrain 4)(ha':A'∈Terrain 4)(hb:B∈Terrain 3)(hc:C∈Terrain 3)(he:A-A'∈Surface 4): Little L a 6 (seqT x y z A B C-seqT x y z A' B C):= by
  apply IsLittleO.congr (Octave.surf t.led t.grant hb hc he) ?_ (fun _=>rfl); exact fun i=>ret_sub ha ha' hb hc (x i) (y i) (z i)
include t in
lemma burnt_b (ha:A∈Terrain 4)(hb:B∈Terrain 3)(hb':B'∈Terrain 3)(hc:C∈Terrain 3)(he:B-B'∈Terrain 4): Little L a 6 (seqT x y z A B C-seqT x y z A B' C):=by
  have ht:= toll3 t.led t.grant ha he hc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); exact (pull (k:=6) t.led ht).congr (fun i=> ret_left ha hb hb' hc (x i) (y i) (z i)) (fun _=>rfl)
include t in
lemma burnt_c (ha:A∈Terrain 4)(hb:B∈Terrain 3)(hc:C∈Terrain 3)(hc':C'∈Terrain 3)(he:C-C'∈Terrain 4): Little L a 6 (seqT x y z A B C-seqT x y z A B C'):=by
  have ht:= toll3 t.led t.grant ha hb he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); exact (pull (k:=6) t.led ht).congr (fun i=>ret_right ha hb hc hc' (x i) (y i) (z i)) (fun _=>rfl)
variable (P Q R:Player W)(g:G.Simple) (σ:Bool)(k:Chiral.P)(i j:Axis)
abbrev M0 (V:Player W): Axis→Toe:= field V.σ V.row -- argument implicit? P preceding
abbrev O := drawn σ k (P.M g)
abbrev home := magnetic σ P.σ k P.row
lemma origin₄ : O P g σ k∈Terrain 4:= (sustained g P.size _ (fun i=>P.α₀ g i) σ k).1
lemma home₄ : home P σ k∈Terrain 4:= tip4 σ P.σ k P.row
lemma tip_local : O P g σ k-home P σ k∈ Surface 4:= drawing _ _ (fun i=> stashed g P.size P.σ P.row P.hr i) σ k
include t in
lemma lost_game (h: P.σ=σ): Little L a 6 (seqT x y z (O P g σ k) (Q.M g i) (R.M g j)-seqT x y z (traceLag k P.row ₹) (Q.M g i) (R.M g j)):=by
  have hh: O P g σ k-traceLag k P.row ₹ ∈ Surface 4:= h ▸ sleeved g P.size P.hr P.σ k P.row; -- h rewrites M? inspect
  have ht: traceLag k P.row ₹ ∈ Terrain 4:= by rw [← sub_sub_self (O P g σ k) (traceLag k P.row ₹)]; exact Submodule.sub_mem _ (origin₄ P g σ k) (light_hill 4 (by norm_num) (surfaces hh))
  exact burnt_a t (origin₄ P g σ k) ht (Q.α₀ g i) (R.α₀ g j) hh
include t in
lemma gold : Little L a 6 (seqT x y z (O P g σ k) (Q.M g i) (R.M g j)-seqT x y z (home P σ k) (M0 Q i) (M0 R j)):=by
  rw [← sub_add_sub_cancel _ (seqT x y z (home P σ k) (Q.M g i) (R.M g j)), ← sub_add_sub_cancel (seqT x y z (home P σ k) (Q.M g i) (R.M g j)) (seqT x y z (home P σ k) (M0 Q i) (R.M g j)) _]; let C:= R.α₀ g j; let D:= home₄ P σ k
  exact IsLittleO.add (burnt_a t (origin₄ P g σ k) D (Q.α₀ g i) C (tip_local P g σ k)) (IsLittleO.add (burnt_b t D (Q.α₀ g i) (bunker Q.σ Q.row i) C (Q.α₁ g i)) (burnt_c t D (bunker Q.σ Q.row i) C (bunker R.σ R.row j) (R.α₁ g j)))
include t in
lemma off_field [NeBot L][L.IsCountablyGenerated] : Payout L a 6 (seqT x y z (O P g σ k) (Q.M g i) (R.M g j)) (parts c σ P.σ k P.row (Q.gCost i) (R.gCost j) u v b):=by
  have he:= Payout.big (gold t P Q R g σ k i j) t.led -- implicit synt
  have hp:= preps c t.led t.x₁ t.x₂ t.x₃ t.gleam (shore Q.σ Q.row i) (shore R.σ R.row j) σ P.σ k P.row
  -- Wait σ=P.σ case: home same derivative kernel includes distribution delta! Works.
  have hh:= hp.add he; rw [add_zero] at hh; apply hh.congr; intro w; unfold seqT; simp only [Pi.sub_apply]; rw [mul_sub]; ring
end YM.XSpace.Finale
