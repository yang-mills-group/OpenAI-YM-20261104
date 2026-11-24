import YM.AllOrder.Ker.Extract
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker
open Lattice Laurent Bloch Matrix Complex RG Push.Uniform Precision Push
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Primitives.TwoWave Primitives.TwoWave.RealSlice Further.PhysicalPeriodLimitF933 Shingle Macrame
open scoped BigOperators Topology Classical ContDiff
variable {n m : Side} {α β : Type} [Fintype α] [Fintype β] {k M : ℕ}
open Macrame.Lace Finset Filter
lemma booking (W:Window n m M)(i:Leaf n α): convey W (spot i)= ∑ u∈parcel (BookM W α) i, spot u:= by
  ext1 x; rw [Finset.sum_apply]; let t:= BookM W α; by_cases h:t x=i; · change spot i (t x)=_; rw [h]; simp only [spot,Pi.single_eq_same];  have hx:x∈parcel (BookM W α) i := (posted ..).mpr h; rw [Finset.sum_eq_single_of_mem x hx (fun a ha hh=> ?_) ] <;> simp_all [eq_comm]
  change spot i (t x)=_; have hz {a x : Leaf m α}(h:x≠a): spot a x=0:=by simp [spot,h]
  rw [show spot i (t x)=0 from (by simp [spot,h])]; symm; exact Finset.sum_eq_zero fun a he=>hz (fun ht=> h ((show t a=i from (posted ..).mp he) ▸ congr_arg t ht))

def pilots (W:Window n m M)(f:Page (Leaf n α) k)(g:Page (Leaf m α) k):Prop := ∀ v,g (convey W ∘ v)=(M:ℝ)*f v

lemma flight (W:Window n m M) {F:rule α n→ℝ}{G:rule α m→ℝ}(hF:ContDiffAt ℝ ω F 0)(hG:ContDiffAt ℝ ω G 0)(H:(fun x=> G (convey W x)) =ᶠ[𝓝 0] fun x=>(M:ℝ)* F x) : pilots W (iteratedFDeriv ℝ k F 0) (iteratedFDeriv ℝ k G 0):= by
 let L:=convey W (α:=α); let q:ℝ:=M; intro v; have he : (G ∘ L)=ᶠ[𝓝 0] q • F:=H; have ht: iteratedFDeriv ℝ k (G ∘ L) 0 v = _ := congr_arg (fun f : Page (Leaf n α) k=> f v) (he.iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds; rw [Next.Foundations.jets_linear L (hG.of_le le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_const_smul_apply (hF.of_le le_top)] at ht; exact ht
omit [Fintype α] in
lemma swiv_eq (w:Site n)(u i:Leaf n α) : turnM α w u=i↔ u=turnM α (-w) i:= by
   obtain ⟨x,y⟩:=u; obtain ⟨z,v⟩:=i; change (x+w,y)=(z,v)↔_; simp [turnM,Macrame.parallel,BookM, ← sub_eq_add_neg,eq_sub_iff_add_eq]
omit [Fintype α] in
lemma swiv (w:Site n)(i:Leaf n α) : convey (Macrame.parallel w) (spot (turnM α w i))=spot i:=by
 funext u; change spot _ (turnM α w u)=_; simp only [spot,Pi.single_apply,swiv_eq]; rcases i with ⟨i,a⟩; simp [turnM,BookM,Macrame.parallel]
lemma pilots.still {G:Page (Leaf n α) (k+1)} (h:∀ w:Site n,pilots (Macrame.parallel w) G G): Stilled (extractF G) := by
 intro w i t; let v:Fin (k+1) → Leaf n α:= (Fin.cons (turnM α w i) (turnM α w ∘ t)); have ht := h w (spot ∘ v); rw [Nat.cast_one,one_mul] at ht; refine ht.symm.trans (congr_arg G ?_); ext1 j; refine Fin.cases (swiv ..) (fun j=> swiv ..) j

lemma always (W:Window n m M)(u x z:Site m) : W.cut (u+(x-z)) = W.cut u+(W.cut x-W.cut z) := by
 let v:=lift (x-z); have hx : x=z+wrap _ v:= by unfold v; rw [wrap_lift, add_sub_cancel]
 nth_rw 2 [hx]; rw [W.port]; rw (occs:=.pos [1]) [show x-z=wrap m v from (wrap_lift ..).symm,W.port]; abel -- edit
omit [Fintype α] in
lemma carried (W:Window n m M){u v:Site m}(h:W.cut u=W.cut v) (z:rule α n) : convey (Macrame.parallel (u-v)) (convey W z)=convey W z:= by funext i; change z (W.cut (i.1+_),i.2)=_; rw [always W _ u v,h,sub_self,add_zero]; rfl

lemma cooks (W:Window n m M){f:Page (Leaf n α) (k+1)}{g:Page (Leaf m α) (k+1)}(hp:0<M)(h:pilots W f g)(H:∀ w:Site m,pilots (Macrame.parallel w) g g): Same (extractF f) (extractF g) W:= by
  let B:=BookM W α; intro i t; let S:=parcel B (B i); let X:=f.curryLeft (spot (B i)); let Y:=convey W ∘ spot ∘ t
  let Z a:=g.curryLeft (spot a) Y
  have hx (u:Leaf m α) (hp:u∈S): Z u=Z i:= by
     let w:Site m:= u.1-i.1; have hu':B u=B i:= (posted ..).mp hp
     have hu : turnM α w i=u:= Prod.ext (by change i.1+(u.1-i.1)=u.1; abel) (congr_arg Prod.snd hu').symm
     let a:Fin (k+1)→ rule α m :=Fin.cons (spot u) Y; have he := H w a; rw [Nat.cast_one,one_mul] at he; apply he.symm.trans (congr_arg g ?_); funext j; refine Fin.cases ?_ ?_ j; · change convey _ (spot u)=_; rw [← hu,swiv w]; rfl
     exact fun j => carried W (α:=α) (congr_arg Prod.fst hu') _ -- ↑u coercions
  let v : Fin (k+1)→ rule α n := Fin.cons (spot (B i)) (spot ∘ t); have ht:=h v;
  rw [show convey W ∘ v = Fin.cons (convey W (spot (B i))) Y from funext fun j=> Fin.cases rfl (fun i=> rfl) j, booking, ← ContinuousMultilinearMap.curryLeft_apply, map_sum,_root_.sum_apply] at ht
  let L:= (M:ℝ); have h' : (∑ j∈S,Z j)=L*Z i:= by rw [Finset.sum_congr rfl (fun j hj=>hx j hj),Finset.sum_const,show S.card=M from seats W _,nsmul_eq_mul]
  have hh : extractF f (B i) t=f v:= congr_arg f (funext fun j=>Fin.cases rfl (fun _=>rfl) j)
  have hb : extractF f (B i) t= Z i:= hh.trans (mul_left_cancel₀ (show (M:ℝ) ≠ 0 by exact_mod_cast hp.ne') (ht.symm.trans h'))
  have hY : Y=fun j:Fin k=> ∑ u∈parcel B (t j),spot u:=funext fun i=>booking ..; rw [hb]; unfold Z; rw [hY,ContinuousMultilinearMap.map_sum_finset]
  have hg : Fintype.piFinset (fun j:Fin k=>parcel B (t j))=robe W t:= by ext v; simp only [Fintype.mem_piFinset,posted,tried]; exact funext_iff.symm
  rw [hg]; exact Finset.sum_congr rfl fun j _=>congr_arg g (funext fun v=>Fin.cases rfl (fun i=>rfl) v)
end YM.AllOrder.Ker
