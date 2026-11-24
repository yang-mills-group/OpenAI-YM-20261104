import YM.MS.Arts.Cabs
import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Spin
/-!
# Split auxiliary real coordinate spaces

Measures remain *Lebesgue*, not the normalized Haar-volume at 4 only;
 convert later with universal beta. Sum decomposition relative to prefix. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {A B:Type}[Fintype A][Fintype B]{m n:ℕ}
omit [Fintype A] [Fintype B] in
lemma look (f:A→B)(p:Momentum B)(i:A): lookG f p i=p (f i):=rfl
variable (h:m≤n)
abbrev Right (h:m≤n):= sendB (aside h)
abbrev Cr (h:m≤n) := lookG (aside h)
-- drop either side
lemma leftCl (p:Momentum (L m)): Cl h (Left h p)=p:= funext fun i=>lasts (rises h) p i
lemma rightCl (p:Momentum (Apart m n)): Cr h (Right h p)=p:= funext fun i=> lasts (aside h) p i
lemma Cl_left (p:Momentum (Apart m n)): Cl h (Right h p)=0:= funext fun i=> offt (aside h) _ _ (fun j=> (nowhere h i j).symm) -- syntax
lemma Cr_down (p: SectorP m): Cr h (Left h p)=0:= funext fun i=> offt (rises h) _ _ (fun j=> nowhere h j i)
lemma city (p:SectorP n) : Left h (Cl h p) + Right h (Cr h p)=p:= by
   ext i; rcases rangeA i h with ⟨j,rfl⟩| ⟨j,rfl⟩; · rw [Pi.add_apply,lasts,offt (aside h) _ _ (fun l=> (nowhere h j l).symm),add_zero]; rfl
   rw [Pi.add_apply,lasts,offt (rises h) _ _ (fun l=>nowhere h l j),zero_add]; rfl
lemma farApart (a b: SectorP n): pairing a b=pairing (Cl h a) (Cl h b) +pairing (Cr h a) (Cr h b):= by
   unfold pairing; rw [cut_sum (R:=ℝ) h]; rfl
lemma pair_zero (p:Momentum A): pairing 0 p=0:=by simp [pairing]
lemma high (a : SectorP m)(b: Momentum (Apart m n)): pairing (Left h a) (Right h b)=0:= by rw [farApart h,leftCl,Cl_left,Cr_down,pair_zero,pair_left a,pair_zero,add_zero] -- hi
lemma sq_up (a:SectorP m): Momentum.sq (Left h a)= Momentum.sq a:= by rw [sq_eq,farApart h,leftCl,Cr_down,pair_zero,add_zero,sq_eq]
lemma sq_down (a:Momentum (Apart m n)): Momentum.sq (Right h a)=Momentum.sq a:= by rw [sq_eq,farApart h,rightCl,Cl_left,pair_zero,zero_add,sq_eq]

def cabs : SectorP n≃L[ℝ](SectorP m × Momentum (Apart m n)) where
    toFun a:=(Cl h a,Cr h a)
    invFun p:= Left h p.1+Right h p.2
    map_add' x y:= by simp
    map_smul' a b:= by simp
    left_inv p:= city h p
    right_inv p:= by simp only [map_add,leftCl,rightCl,Cl_left,Cr_down,add_zero,zero_add]
    continuous_toFun:= (Cl h).continuous.prodMk (Cr h).continuous
    continuous_invFun:= by fun_prop

lemma cab (v:SectorP n)(i:L m): (cabs h v).1 i=v (rises h i):= rfl
lemma abc (v:SectorP n)(i:Apart m n): (cabs h v).2 i=v (aside h i):= rfl
lemma cabs_measure : MeasurePreserving (cabs h):= by
   let πF:=fun i:L n=> (volume:Measure ℝ); let Y:= equivS h; let M:= MeasurableEquiv.piCongrLeft (fun _:L n=>ℝ) (equivS h); let V:= MeasurableEquiv.sumPiEquivProdPi (fun _:L m ⊕ Apart m n=>ℝ); obtain he:= (measurePreserving_sumPiEquivProdPi (fun i:L m ⊕ Apart m n=> πF (Y i))).comp (measurePreserving_piCongrLeft πF Y).symm; convert! he using 1
end YM.MS.Arts
