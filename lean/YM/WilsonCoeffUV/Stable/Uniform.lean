import YM.WilsonCoeffUV.Stable.Yield
/-!
# Strict operations cost polynomial in level currency, linear in continuing fuel

Includes synchronized holog basis-independent step; does *not* count period tests.
Θ=t scales capture/reference for untested operations. Becomes native for mark.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{U V E:Type*}{r h D l j e k a m t u:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X B C δ:ℝ}

section
variable [NormedAddCommGroup V] {I:Type*}{J:I→Type*}{α β:I→Type*}
variable {o:(i:I)→J i→Cover}{x θ η y:(i:I)→J i→ℝ}
structure Meter {I:Type*}{J:I→Type*}(x θ η y:(i:I)→J i→ℝ) : Prop where
   shine :∀ i,Brite (x i) (θ i)
   charges i:0≤η i
   post i:0≤y i

def Fallow (o:(i:I)→J i→Cover)(u:ℕ)(x θ η y:(i:I)→J i→ℝ)(P Q:(i:I)→J i→ Ten V (Cloth (α i)) r): Prop := ∃ d:ℕ,∀ i,∃ C:ℝ,0≤ C ∧∀ j,YieldP (o i j) (η i j) u (C*x i j^d*y i j) (θ i j) (P i j) (Q i j)
variable {P Q A B:(i:I)→J i→ Ten V (Cloth (α i)) r}
lemma Fallow.plus(p:Fallow o u x θ η y P Q)(q:Fallow o u x θ η y A B)(h:Meter x θ η y): Fallow o u x θ η y (P+A) (Q+B):=by
    obtain ⟨d,H⟩:=p; obtain ⟨e,T⟩:=q; refine ⟨d+e,fun i=>?_⟩; obtain ⟨A,hA,u⟩:= H i; obtain ⟨B,hB,g⟩:= T i
    refine ⟨A+B,add_nonneg hA hB,fun j=> ((u j).plus (g j) (h.charges i j)).step ?_ ((h.shine i).dist _)⟩
    rw [←add_mul]; exact mul_le_mul_of_nonneg_right (roof_pair _ _ _ ((h.shine i).large j) hA hB _ _) (h.post i _)
lemma Fallow.zero:Fallow o u x θ η y (0:(i:I)→J i→ Ten V (Cloth (α i)) r) 0:= ⟨0,fun i=>⟨0,le_rfl,fun j=> by rw [zero_mul,zero_mul]; exact YieldP.zero⟩⟩
lemma Fallow.sum {S:Finset U}{P Q: U→(i:I)→ J i→ Ten V (Cloth (α i)) r}(p:∀ i∈S,Fallow o u x θ η y (P i) (Q i))(h:Meter x θ η y): Fallow o u x θ η y (fun i j=>∑ k∈S,P k i j) (fun i j=>∑ k∈S,Q k i j):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Fallow.zero
    | @insert i S e ih=> simp_rw [Finset.sum_insert e]; exact (p i (Finset.mem_insert_self ..)).plus (ih fun j hj=> p j (Finset.mem_insert_of_mem hj)) h
lemma Fallow.gleanS {P Q:(i:I)→J i→ Ten V (Cloth (α i⊕β i)) r}(p:Fallow o u x θ η y P Q): Fallow o u x θ η y (fun i j=>scoop (P i j)) (fun i j=>scoop (Q i j)):=by
    obtain ⟨d,H⟩:= p; refine ⟨d,fun i=>?_⟩; obtain ⟨c,h,g⟩:= H i; exact ⟨c,h,fun j=> (g j).gleanP⟩
lemma Fallow.st [NormedSpace ℝ V] {v w:(i:I)→J i→ℝ}(t:Slate x θ v w)(p:Fallow o u x θ η y P Q)(h:Meter x θ η y): Fallow o u x θ η y (fun i j=> v i j • P i j) (fun i j=>w i j • Q i j):=by
    obtain ⟨d,H⟩:=p; obtain ⟨n,T⟩:=t; refine ⟨d+n,fun i=>?_⟩; obtain ⟨A,a,g⟩:= H i; obtain ⟨B,b,f⟩:= T i; refine ⟨2*A*B,by positivity,fun j=>?_⟩
    rw [show _ * x i j^(d+n)*y i j= 2*(A*x i j^d*y i j)*(B*x i j^n) from by rw [pow_add]; ring]; exact (g j).mag (f j) (h.charges i j)
end

section
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
variable {U: (_:Gear G)→Type*}(o: (I:Gear G)→ U I→Cover) (η y: (I:Gear G)→ U I→ℝ) (T: (I: Gear G) → U I→ Rally (e+1) 0 I)

def xpos (e:ℕ)(T:(I:Gear G) → U I→ Rally (e+1) 0 I)(i: Gear G)(v):= (T i v).x
def dpos (e:ℕ)(T:(I: Gear G) → U I→ Rally (e+1) 0 I)(i: Gear G)(v):= (T i v).σ
variable {T}
lemma herb_pt {α β:Type*} {G:ropes Cover α β}(h:dragCup Bank.terrain s C G)(p:0≤s)(i j): ‖G i j‖ ≤ C:=by simpa using (h.mono p).2 i j
variable {W Z:(I:Gear G)→ U I→Layers V (Cloth (Helms I))}
lemma meadow (g:Meter (xpos e T) (dpos e T) η y)(f:∀ i,η i≤1)(l:m≤ e)(h:∀ i≤k,∀ j<m,∀ r, Fallow o u (xpos e T) (dpos e T) η y (fun M x=> W M x i j r) (fun M x=>Z M x i j r))
  (P Q:(I:Gear G)→U I→ ropes Cover (Helms I) (Helms I))(hp:∀ i j,Ballast i.σ i.D (dpos e T i j) (P i j) (Q i j))(r:ℕ) : Fallow o u (xpos e T) (dpos e T) η y (fun i j=> Soil.paintC (P i j) ((T i j).P.rays) (W i j) k m r) (fun i j=> Soil.paintC (Q i j) ((T i j).Q.rays) (Z i j) k m r):=by
   simp_rw [Soil.paintC,Finset.sum_apply]; apply Fallow.sum _ g; intro i hi; apply Fallow.sum _ g; intro j hj
   have ht:= Finset.mem_antidiagonal.mp hi; have he:= Finset.mem_antidiagonal.mp hj; simp_rw [rondel]; apply Fallow.sum _ g; intro x hx; have hv:= Finset.mem_antidiagonal.mp hx
   by_cases hh:j.1=0
   · have H (I:Gear G)(M)(T:Stand I)(Y:Gen V (Cloth (Helms I))): ruins (swivel (rill M (T.rays i.1 j.1) Y r x.1 x.2))=0:=by
        rw [hh,show T.rays i.1 0=0 from T.negative _]; funext v; unfold ruins swivel; simp_rw [Pi.smul_apply,Finset.sum_apply];
        obtain ⟨l,k⟩:= x; change l+k=r at hv; subst r; simp_rw [rill_spell]; simp
     simp_rw [H]; exact Fallow.zero
   obtain ⟨d,H⟩:= Satin.flywheel (G:=G) i.1 j.1 (x.1+1) (e+1) 0 (Or.inl (by omega)) Gear.σ Gear.holds (fun I=> I.price.le)
   obtain ⟨a,F⟩:= h i.2 (by omega) j.2 (by omega) (x.2+1); refine ⟨a+d,fun i=>?_⟩
   obtain ⟨C,c,f'⟩:=F i; obtain ⟨A,v,q⟩:= H i
   have hu:= tender_nn i.price (Helms i) u; have hb:=piped_nn (β:=Helms i) x.1 i.price u; have ht:=zero_le_one.trans i.bill_nn; let S:= pegPrice x.1 x.2; have hs:0≤ S:=by unfold S pegPrice; positivity
   refine ⟨3*S*(C*(i.D*tender (Helms i) i.σ u*(A*piped (Helms i) x.1 i.σ u))),by positivity,fun w=>?_⟩
   have hp := YieldP.tap i.price (y:=q (T i w)) (f' w) (hp i w) hv (g.charges i w) (f i w)
   rw [pow_add]; convert! hp using 1; unfold xpos largus; ring

-- just heap generator payoff for time cut <height caps
lemma stadium (g:Meter (xpos e T) (dpos e T) η y) (f:∀ i,η i≤1)(F P:(I:Gear G) → U I→Pal V (Cloth (Helms I)))
   (b:∀ i j, lowerGrade i j e l → Fallow o u (xpos e T) (dpos e T) η y (fun m x=> F m x i j) (fun m x=>P m x i j)) (r:ℕ)(z:m<e∨m=e∧l< r+2*k) : Fallow o u (xpos e T) (dpos e T) η y (fun i j=> let t:=(T i j).P; heap t.payMat t.rays (F i j) k m r) (fun i j=> let t:=(T i j).Q; heap t.payMat t.rays (P i j) k m r):=by
   induction k using Nat.strong_induction_on generalizing r m with
   | h n ih=>
     cases n with
     | zero=> simp only [level]; exact b _ _ (by unfold lowerGrade; omega)
     | succ n=>
       let X: (I:Gear G)→U I→ Layers V (Cloth (Helms I)) := fun i j=> heap ((T i j).P.payMat) ((T i j).P.rays) (F i j); let Y: (I:Gear G)→ U I→ Layers V (Cloth (Helms I)):=fun i j=>heap ((T i j).Q.payMat) ((T i j).Q.rays) (P i j)
       have hh a (hu:a≤ n) (j) (v:j<m)(b): Fallow o u (xpos e T) (dpos e T) η y (fun i k=>X i k a j b) (fun i k=> Y i k a j b):= ih a (by omega) b (Or.inl (by omega))
       let A i j:=(T i j).P.payMat; let B i j:=(T i j).Q.payMat
       have ht i j:= (pm_rate (T i j)).mono i.holds.le
       have hv:= meadow o η y g f (show m≤e by omega) hh A B ht r
       have hq:= meadow o η y g f (show m≤ e by omega) hh (fun i j=>(A i j).transpose) (fun i j=>(B i j).transpose) (fun i j=> Cosmos.BankT (ht i j)) r
       obtain ⟨d,H⟩:= ih n n.lt_succ_self (r+2) (show m<e∨m=e∧l< r+2+2*n from by omega)
       have hy : Fallow o u (xpos e T) (dpos e T) η y (fun i j=> rime (A i j) (X i j n m) r) (fun i j=>rime (B i j) (Y i j n m) r):=by
          refine ⟨d,fun i=>?_⟩; obtain ⟨a,hA,hR⟩:= H i; have he: 0≤fareV r:=by unfold fareV; positivity;
          have hk:=zero_le_one.trans i.bill_nn
          refine ⟨2*i.D*a*fareV r,by positivity,fun x=>?_⟩
          convert! (hR x).rimeX (g.charges i x) (A i x) (B i x) hk (ht i x).between.1 (herb_pt (ht i x).oneP i.price.le) (herb_pt (ht i x).otherP i.price.le) (herb_pt (ht i x).between i.price.le) using 1; ring
       simp only [inchC,Pi.smul_apply]; exact Fallow.st (Slate.one (P:=fun _=> ((n+1:ℕ):ℝ)⁻¹) g.shine) ((hy.plus hv g).plus hq g) g
end
end YM.WilsonCoeffUV.Shard
