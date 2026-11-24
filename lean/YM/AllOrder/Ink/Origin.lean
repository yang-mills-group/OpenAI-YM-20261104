import YM.AllOrder.Ink.Merge
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
section base
variable (F: Fan α α k) (T : Page (Leaf n α) (k+1))(Y:rule α n)
def shine (t:Fin k→α) (x:Shift (Arm k)) := List.ofFn fun i:Fin k=> ((point x i,t i):Point α)
def strand (F:Fan α α k)(r:α): Field α where
 Ty:= Shift (Arm k) × (Fin k→α)
 slip i:= (0,r)::shine i.2 i.1
 fee i:= F r i.2 i.1
lemma chalk {t:Fin k→α} (x:Shift (Arm k)): meter (shine t x) = size x:= by simp [meter,shine,List.sum_ofFn,size]; rw [Fintype.sum_prod_type]; rfl
variable (hF:Cap F a C) (hC:0 ≤ C) (ha:0≤a)
omit [Fintype α] in
lemma sunny (x:Site n)(t:Fin k→α)(w:Shift (Arm k)) : invoice x (shine t w) Y= ∏ i,Y (floated x t w i):=by simp [shine,invoice,paid,List.prod_ofFn]; rfl
include hF ha in
lemma lighting (x:Site n)(r:α): drive (pieces F n) (fun _=>Y) (x,r) = ∑' w : Shift (Arm k), ∑ j:Fin k→α,F r j w*invoice x (shine j w) Y:= by
   let H t w:= if t=floated x (Prod.snd ∘ t) w then F r (Prod.snd ∘ t) w else 0
   let i:Leaf n α:=(x,r); let u (t:Fin k→Leaf n α):=∏ s,Y (t s)
   have ht (t:Fin k→Leaf n α):= (hF.pencils ha i (t:Fin k→_)).mul_right (u t)
   change _= _; let f t w:= H t w*u t; have he (t:Fin k→Leaf n α): HasSum (f t) (pieces F n i t*u t):=ht t
   unfold drive; rw [← (hasSum_sum (s:=Finset.univ) (fun t _=> he t)).tsum_eq]; apply tsum_congr; intro w
   let l (t:Fin k→α):= floated x t w; have hi:Injective l:= fun a b h=>congr_arg (fun z:Fin k→Leaf n α=> Prod.snd ∘ z) h
   rw [show ∑ t:Fin k→Leaf n α,f t w=∑ t∈Finset.univ.image l,f t w from ?_, Finset.sum_image hi.injOn]; swap;
   · symm; apply Finset.sum_subset (Finset.subset_univ _); intro t h ho; unfold f H; split; rename_i hh; · exact (ho (hh.symm ▸ Finset.mem_image_of_mem l (Finset.mem_univ _))).elim
     exact zero_mul _
   refine Finset.sum_congr rfl fun j _=>?_ ; unfold f H; rw [if_pos (show l j=floated x (Prod.snd ∘ l j) w from rfl),sunny]; rfl

include hF hC
lemma letter (v:α): (strand F v).Good a ((Fintype.card (Fin k→α):ℝ)*C) (k+1):= by
 let G:=strand F v; have hc(j:Fin k→α):= hF v j
 refine ⟨fun i=>by change List.length ((0,v)::shine _ _)≤_; simp [shine],?_⟩; let f(i:G.Ty):= G.price a i
 have hp(t:Fin k→α):SumBudget (fun w:Shift (Arm k)=> f (w,t)) C:= by unfold f Field.price G; simp_rw [strand, show ∀ r:α,∀ w:Shift (Arm k),meter ((0,r)::shine t w)=size w from fun r w=>by change size (0:Cover)+meter (shine t w)= _; rw [chalk]; simp [size]]; exact hF v t
 apply budget_fiberwise (C:=((Fintype.card (Fin k→α):ℝ)*C)) (f:=fun i:G.Ty=>f i) (fun i:G.Ty=> i.2) (fun i=> G.price_nonneg ..) ?_ (budget_finite (fun i:Fin k→α=>hC) (by simp)); intro j S hs
 let v:= S.image (fun i:G.Ty=>i.1)
 refine le_trans (le_of_eq ?_) (budget_sum (hp j) v); rw [Finset.sum_image]; swap
 · intro i hi w hw h; exact Prod.ext h ((hs _ hi).trans (hs _ hw).symm)
 exact Finset.sum_congr rfl fun i hi=> (hs i hi) ▸ rfl -- risk index

def principal (F: Fan α α k): Field α:= Field.sum (strand F)
lemma pride : (principal F).Good a ((Fintype.card α:ℝ)* ((Fintype.card (Fin k→α):ℝ)*C)) (k+1):= Field.keep (strand F) (letter F hF hC) (budget_finite (fun i=>by positivity) (by simp))
include ha
lemma dawn (x:Site n) (i:α): (strand F i).site n x Y= Y (x,i)* drive (pieces F n) (fun _=>Y) (x,i) :=by
 let G:=strand F i; let f (j:G.Ty):= G.fee j* invoice x (G.slip j) Y; rw [lighting F Y hF ha,← tsum_mul_left]; change (∑' j:Shift (Arm k) × (Fin k→α), f j)=_; rw [((letter F hF hC i).total ha x Y).tsum_prod]; apply tsum_congr; intro q; rw [tsum_fintype,Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; change F i s q* (Y (stood x (0,i))*invoice x (shine s q) Y)=_; simp only [stood,map_zero,add_zero]; ring
omit hF hC ha in
lemma pose : T (fun _=>Y)=∑ i:Leaf n α, Y i * drive (extractF T) (fun _=>Y) i:= by
 let R:= T.curryLeft; let g:=fun (_:Fin k)=> Y; let f(i:Leaf n α):= spot i; have hz : ∑ i:Leaf n α, Y i • f i=Y := combine Y
 let P(i:Leaf n α):= R (f i); have hu(i:Leaf n α): P i g=drive (extractF T) g i := by
    rw (occs:=.pos [1]) [show g=(fun _=> ∑ i:Leaf n α, Y i • f i) from funext fun _=>hz.symm]
    -- switch multilinear
    change (P i).toMultilinearMap _ = _; rw [MultilinearMap.map_sum_finset, Fintype.piFinset_univ]; unfold drive; refine Finset.sum_congr rfl (fun t _=>?_); rw [MultilinearMap.map_smul_univ,smul_eq_mul,mul_comm]; apply congr_arg (·* ∏ s,Y (t s)); exact congr_arg T (funext fun k=> Fin.cases rfl (fun j=>rfl) k)
 rw [show (fun _:Fin (k+1)=>Y)=Fin.cons (∑ i:Leaf n α,Y i • f i) g from ?_, ← ContinuousMultilinearMap.curryLeft_apply,map_sum,_root_.sum_apply]; swap; · rw [hz]; exact funext (fun i=> Fin.cases rfl (fun j=>rfl) i)
 refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,_root_.smul_apply]; exact congr_arg (Y i *·) (hu i) -- R reducible
lemma beginning {T: Page (Leaf n α) (k+1)} (h:extractF T=pieces F n) : (principal F).table n Y=T (fun _=>Y):= by
 unfold principal; rw [Field.contribution _ (letter F hF hC) (budget_finite (fun _=> mul_nonneg (Nat.cast_nonneg _) hC) (show (∑ i:α,(Fintype.card (Fin k→α):ℝ)*C) ≤ (Fintype.card α:ℝ)*((Fintype.card (Fin k→α):ℝ)*C) by simp)) ha, Finset.sum_apply, pose,h,Fintype.sum_prod_type]; simp_rw [Field.table_apply,dawn F Y hF hC ha]; exact Finset.sum_comm
end base
end YM.AllOrder.Ink
