import YM.RemainderComparison.Encore.Inks
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Set MeasureTheory Marker Finset MonoidWithZeroHom
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open GridRenewal.Rain Flues Push.AbsoluteSums
variable {θ ι α : Type} [DecidableEq θ]{J : Census θ}
variable (f :ι→ Option α) (g:ι→ Poly J)(V:α→ Poly J)
variable {q:θ→ℝ} (h:∀ i,0<q i) (hg:Summable (fun i=> Poly.price q (g i))) (hV:Summable (fun i=> Poly.price q (V i)))
-- require cost inputs NOT coefficient cardinal factor.
def Realm := {x: Finset ι × Finset α| unique f x.1 ∧ token f x.1 ⊆ x.2}
def ringX (v:ι→ℝ)(u:α→ℝ)(x:Finset ι× Finset α):= ((∏ i∈ x.1,v i) * ∏ i∈x.2,u i)
def eraseX (x: ↑(Realm f)) := (x.val.1,x.val.2 \ token f x.val.1)
lemma saves : Function.Injective (eraseX f) := by rintro ⟨⟨u,b⟩,hb⟩ ⟨⟨w,b'⟩,hw⟩ he; change (u,b \_)= (w,b'\_) at he; obtain ⟨rfl,hp⟩:= Prod.mk.inj he; change (b\token f u)=(b'\ token f u) at hp; have h:b=b':=(Finset.sdiff_union_of_subset (show token f u⊆b from hb.2)).symm.trans ((congr_arg (· ∪ token f u) hp).trans (Finset.sdiff_union_of_subset hw.2)); congr

include h hg hV
omit hV hg in
lemma cap (x:Realm f): Poly.price q (chop f g V x.val.1 x.val.2) ≤ ringX (fun i=>Poly.price q (g i)) (fun i=>Poly.price q (V i)) (eraseX f x):=by
    unfold chop
    rw [if_pos (show unique f x.val.fst∧token f x.val.fst⊆ x.val.snd from x.prop)]
    apply (Poly.multiplication h ..).trans; exact mul_le_mul (Poly.multiple h x.val.1 g) (Poly.multiple h (x.val.snd \ token f x.val.1) V) (Poly.nonnegative h _) (Finset.prod_nonneg (f:=fun j=>Poly.price q (g j)) fun i _=>Poly.nonnegative h _)
omit h hg hV in
lemma summable_ring {f:ι→ℝ}{g:α→ℝ}(h : Summable f) (he : Summable g)(hh:∀ i,0≤ f i)(hp:∀ i,0≤ g i) : Summable (ringX f g):= by
   let F x:= ∏ i∈(x:Finset ι),f i; let Gs (x:Finset α):= ∏ i∈x,g i; have hv : Summable F:=summable_finsetProd_of_summable_nonneg hh h; have ht : Summable Gs:=summable_finsetProd_of_summable_nonneg hp he; have he : Summable (fun x:Finset ι×Finset α=> F x.fst*Gs x.snd):= Summable.mul_of_nonneg (f:=F) (g:=Gs) hv ht (fun s=> show 0≤ F s from Finset.prod_nonneg fun i _=>hh i) (fun s=> show 0≤ Gs s from Finset.prod_nonneg fun i _=>hp i); exact he
omit h hg hV in
lemma deployed : Function.support (fun (x:Finset ι×Finset α)=> chop f g V x.1 x.2) ⊆ Realm f :=fun s hs=>Classical.byContradiction fun he=> hs (show chop f g V s.1 s.2=0 from if_neg he)
local notation "G₀"=> ringX (fun i=>Poly.price q (g i)) (fun i=>Poly.price q (V i)) ∘ eraseX f
lemma muster : Summable G₀:=by
    let v (i:ι):= Poly.price q (g i); let b (i:α):= Poly.price q (V i); have he: Summable (ringX v b):=summable_ring (f:=v) (g:=b) hg hV (fun i=>Poly.nonnegative h (g i)) (fun i=> Poly.nonnegative h (V i))
    have hb: Summable (ringX v b ∘ eraseX f):= he.comp_injective (i:=eraseX f) (saves f)
    exact hb
lemma stock : Summable (fun i:Realm f=> chop f g V i.val.1 i.val.2):=by
    let F i:=chop f g V (i:Realm f).val.fst i.val.snd
    have ht(i:Realm f): Poly.price q (F i) ≤ G₀ i:=cap f g V h i
    exact (Poly.budgeted (M:=Realm f) (f:=F) (b:=G₀) h (muster f g V h hg hV) ht).1
lemma tally : Summable (fun x:Finset ι× Finset α=> chop f g V x.1 x.2):=((hasSum_subtype_iff_of_support_subset (deployed f g V)).mp (stock f g V h hg hV).hasSum).summable

def eatS (j:α) := V j +∑' i:ι,if f i=some j then g i else 0
variable [Fintype θ]
set_option maxHeartbeats 500000 in
lemma alive(c:Finset α) (u :ι→Poly J)(hu:Summable u) (he:∀ i,cyclone (u i)= if f i=none then 1+g i else 1):
          ∑' s,chop f g V s c= cyclone (∑' i,u i)*∏ i∈c,eatS f g V i:=by
   let F s:= chop f g V s c; have hF : Summable F:= (tally f g V h hg hV).comp_injective (i:=(fun x:Finset ι=>(x,c))) (fun a b h=> (Prod.mk.inj (show (a,c)=(b,c) from h)).1)
   have ht : Tendsto (fun v:Finset ι=> ∑ s∈v.powerset,F s) atTop (𝓝 (∑' i,F i)):= hF.hasSum.comp tendsto_finset_powerset_atTop_atTop
   have hQ i : Tendsto (fun s:Finset ι=>leaf f g V s i) atTop (𝓝 (eatS f g V i)):=by
       have hs : Summable (fun j:ι=> if f j=some i then g j else 0):= (Poly.budgeted h hg fun j=>by split; exact le_rfl; rw [Poly.zero_price]; exact Poly.nonnegative h _).1
       exact Tendsto.const_add (V i) hs.hasSum
   simp_rw [F,holiday,← he,← roaring] at ht
   have Hμ : Tendsto (fun z:Finset ι=> cyclone (∑ i∈z,u i) * ∏ i∈c,leaf f g V z i) atTop (𝓝 (cyclone (∑' i,u i)*∏ i∈c,eatS f g V i)) := Tendsto.mul (f:=fun z=> cyclone (∑ i∈z,u i)) (g:=fun z=> ∏ i∈c,leaf f g V z i) (GridRenewal.Rain.breath.continuousAt.tendsto.comp hu.hasSum) (tendsto_finsetProd (f:=fun i s=>leaf f g V s i) c fun i _=>hQ i)
   exact tendsto_nhds_unique ht Hμ
end YM.RemainderComparison.Encore
