import YM.MS.City.WithEdges
/-!
# Keeping the global color action exact

First test on finite rows in momentum, then all real t via observed-leg truncations.
 Translation restrict as needed only for tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color
open Native.Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H: Detect.Law G} {s: Finset QP} (K:YMflow Axis)(T:QP→QP){b:Bool} (u:G.El)

local notation "W"=> repeatC (D:=Axis) (P:=QP) u
local notation "B"=> Landau.choir (C:=CI G) K T
local notation "V"=>field (P:=QP) (Landau.parity (A:=Axis) (C:=CI G))
lemma porch (i j:Atom Axis)(q:QP): ∑ k:CI G,Koszul.D ((i,k),q) (Koszul.D ((j,k),-q) (W F))= W (∑ k:CI G,Koszul.D ((i,k),q) (Koszul.D ((j,k),-q) F)):= by
    simp_rw [c_prefix,map_sum,map_smul,c_prefix, Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; simp only [setLeg]; simp_rw [← Finset.sum_smul,forward]; simp [ite_smul]
lemma line_at (q:QP): repeatC u (trc (Landau.choir K T) q F)= trc (B) q (W F):= by
   have he (K: YMflow Axis) (F:Detect.Law G) : trc (Landau.choir K T) q F=∑ j:Atom Axis,∑ a: Atom Axis, (K j a (T q)) • (∑ i:CI G,diffPair ((j,i),q) ((a,i),-q) F):= by
       simp only [trc,LinearMap.sum_apply, LinearMap.smul_apply]; simp_rw [Fintype.sum_prod_type, Landau.choir]; simp only [ite_smul,zero_smul, Fintype.sum_ite_eq,Finset.smul_sum];
       exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun i _=> by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm)
   simp_rw [he,map_sum,map_smul,diffPair_apply]; have hv j i  : (∑ k:CI G,D ((i,k),-q) (D ((j,k),q) (W F)))= W (∑ k:CI G, D ((i,k),-q) (D ((j,k),q) F)) := by simpa only [neg_neg] using porch u i j (-q) (F:=F); -- right expr missing
   simp_rw [hv] -- map_sum expanded rhs W; catch
open Classical in
lemma tr_unique (x: QP) (f: Detect.Law G)(s:Finset QP): trc (trim s B) x f= if x∈s then trc B x f else 0:= by
    classical
    unfold trc trim; by_cases h:x∈s <;> simp [*] -- finset syntax
lemma color_slab : W (slab (trim s B) s F)= slab (trim s B) s (W F):= by
    unfold Flux.slab; simp only [LinearMap.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [tr_unique,if_pos hi,tr_unique,if_pos hi,line_at]
lemma translateD : translate (W F)=W (translate F):= by
   ext w; by_cases hs:net w=0; swap; · rw [trans_off _ _ hs]; exact Eq.symm (High.paint_zero u w (fun l h=> trans_off F l (fun he=> hs (High.paint_course h (fun _=> he) rfl))))
   rw [trans_on _ _ hs]; exact High.paint_congr u w (fun l hl=> Eq.symm (trans_on F l (High.paint_course (Eq.symm hl) (fun _=> hs) rfl))) -- implicit b?
lemma link_slab (s:Finset QP) : repeatC u (link (slab (trim s B) s) b V F H)=link (slab (trim s B) s) b V (W F) (W H):= by
   unfold link; rw [map_sub,map_sub,color_slab]; simp_rw [show ∀ F G:Detect.Law G,W (product V F G)=product V (W F) (W G) from fun f g=> Lifting.linkC _, color_slab,show W (sign V b F)= _ from Lifting.riseC u] -- sign notation
lemma tree_dye (h:closed B parity b): W (tree parity B F H)=tree parity B (W F) (W H):= by
   obtain hx : ∀ s:Finset QP, W (tree parity (trim s B) (translate F) H)=tree parity (trim s B) (translate (W F)) (W H):= by intro s; rw [stickT h s (trans_off F), stickT h s (trans_off (W F)), translateD,link_slab]
   ext l; let Ω := atTop (α:=Finset QP);
   have ht (wG:Finset QP→ Landau.Detect.Law G)(P:Landau.Detect.Law _)(h:∀ i, ∀ᶠ s in Ω, wG s i=P i)(w): ∀ᶠ s in Ω,W (wG s) w=W P w:= by
        induction w generalizing wG P with
        | nil=>exact h _
        | cons i l ih=>
           simp_rw [repeat_cons]; refine finadd _ _ _ fun j _=> ?_; filter_upwards [ih (fun s=>D (setLeg i j) (wG s)) (D (setLeg i j) P) (fun l=> h (setLeg i j::l))] with s hs; rw [hs]
   obtain ⟨s,hv,hZ⟩:= ((ht (fun s=> tree parity (trim s B) (translate F) H) _ (fun i=>roll_tree parity (translate F) H B i) l).and (roll_tree parity (translate (W F)) (W H) B l)).exists
   rw [← tree_trans (F:=F),← tree_trans (F:=W F), ← hv, ←hZ,hx]
lemma cycle_dye (μ: Measure QP)(h: Pass B F μ): W (Ccy B F μ)= Ccy B (W F) μ:= by
    ext l; unfold Ccy; rw [Color.rep_integral (j:=u) (μ:=μ) (f:=fun t=> trc B t F) h l]; simp_rw [line_at]
end YM.MS.City
