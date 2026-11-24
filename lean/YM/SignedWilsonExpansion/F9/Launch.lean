import YM.SignedWilsonExpansion.F9.Foyer
/-!
# Top rank-resolving plot for all epochs

Restore H orientation by whole offshell orbit -- including Ward and
lower-rank projections. This makes the coupling-dependent solver a legitimate
orientation on the test file matrix; Ward is exact at separated test distance
(before any limit and after taking all faces in the book together!). `symmetric`
means the launch, not kinetics in the separately regulator-priced names.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Pill Cloth
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {G:Gauge}{H:Hol G}{h i j k m r d n l:ℕ}{F:Frame G h}{x: Label G h}
variable (F:Frame G h)
noncomputable abbrev realM (s:Signed) := bleached F s.ortho
lemma realM_turn (s t:Signed)(i j:F.Index): realM F (s*t) i j = ∑ x:F.Index, realM F s i x*realM F t x j:=by
   unfold realM; change (F.act (s*t).ortho (Pi.single j 1) i).re=_; rw [show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO s t,Frame.act_mul]; exact pulp F ..
lemma realM_id (i j:F.Index): realM F 1 i j = if i=j then 1 else 0:= by unfold realM bleached; rw [show Signed.ortho 1=1 from map_one Signed.inclusionO,Frame.act_one]; by_cases hi:i=j; simp [hi]; simp [hi,Ne.symm hi]
section
variable {E:Type*}[AddCommGroup E][Module ℝ E](x:F.Index→E)(L:Signed→Module.End ℝ E)(q:∀ s t v, L s (L t v)=L (s*t) v)
def faux (s:Signed)(j:F.Index): E:= ∑ i:F.Index, realM F s⁻¹ i j • L s (x i)
def bandage (j:F.Index): E:= ((Fintype.card Signed:ℝ)⁻¹) • ∑ s:Signed,faux F x L s j
include q
lemma care (s t:Signed)(i:F.Index): L t (faux F x L s i)= ∑ j:F.Index, realM F t j i • faux F x L (t*s) j:=by
    unfold faux; rw [map_sum]; simp_rw [map_smul, q]; simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm (s:=Finset.univ) (f:=fun j a=> (realM F t j i * realM F (t*s)⁻¹ a j) • L (t*s) (x a))]; apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_smul, ← show (∑ a, realM F t a i * realM F (t*s)⁻¹ j a)= realM F s⁻¹ j i from ?_]
    exact (Finset.sum_congr rfl (fun a (_:a∈Finset.univ)=> mul_comm (realM F t a i) (realM F (t*s)⁻¹ j a))).trans ((realM_turn F (t*s)⁻¹ t j i).symm.trans (by rw [show (t*s)⁻¹*t= s⁻¹ by simp]))

lemma band_turn (s:Signed)(i:F.Index): L s (bandage F x L i) = ∑ j:F.Index, realM F s j i • bandage F x L j:=by
    unfold bandage; rw [map_smul,map_sum]; simp_rw [care F x L q _ s i]; rw [Finset.sum_comm]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.smul_sum, show (∑ b,faux F x L (s*b) j)=_ from Equiv.sum_comp (Equiv.mulLeft s) (fun q=> faux F x L q j)]; exact smul_comm ..
end

variable {F}
abbrev Stove (F:Frame G h)(k:ℕ):= F.Index→Cloth G k
variable (H:Hol G)
abbrev fetch {L:Frames G}(A:∀ h,XSpace.Survey G H h)(R:∀ h, Rays G h H)(v:h≤k) : Stove (L.level h) k:= fun i=> Cloth.raiseC ((value_le (L.level h) i).trans v) (elder A R L i)
-- simpler Facts: birth row at bottom etc. NEED lemma rotate_up. add
lemma Cloth.uprights (s:Signed)(p:r≤k)(x:Cloth G r): rotate s k (Cloth.raiseC p x)=Cloth.raiseC p (rotate s r x):=by
    apply recCloth x ?_ ?_; · simp only [map_zero]
    intro A B h i c he; simp_rw [map_add,map_smul,he,upRaise,rolled]; rw [upRaise]
section podium
variable {L:Frames G} (A:∀ h, XSpace.Survey G H h)(R:∀ h, Rays G h H)(v:h≤ k)
def notesT : Stove (L.level h) k:= bandage (L.level h) (fetch H A R v) (fun s=>rotate s k)
local notation "φ" => @notesT G H h k L A R v
lemma envoy (s:Signed) : MotionP (L.level h) s (photo ∘ (notesT (L:=L) H A R v)):=by
    intro i; let P:= fetch (L:=L) H A R v; let F:= L.level h; let XΩ (s):= rotate (G:=G) s k; let w (i):= bandage F P XΩ i
    have ht: ∑ j, realM F s j i • photo (w j) = photo (XΩ s (w i)):=by unfold w photo; rw [band_turn F P XΩ (fun s t=> rotate_mul s t) s i,map_sum]; simp_rw [map_smul];
    dsimp only [Function.comp_apply]; exact (congrArg (Roll s (photo (w i))) ht.symm) ▸ revolt (w i) s
lemma posts_rank (x:(L.level h).Index) (e:wr (L.level h) x< r): ((notesT (L:=L) H A R v x).photo).2 0 r=0:=by
    let F:= L.level h; let P: Stove F k:= fetch H A R v; let D:= bandage F P (fun s=>Cloth.rotate s k); change (photo (D x)).2 0 r=0
    unfold photo D bandage faux; simp only [map_smul,map_sum, Prod.snd_sum, Prod.smul_snd,Pi.smul_apply, Finset.sum_apply]; suffices he : ∀s:Signed, ∀ i, realM F s⁻¹ i x • (liftsC G k (rotate s k (P i))).2 0 r=0 by simp_rw [he,Finset.sum_const_zero,smul_zero]
    intro s i; by_cases h:F.grades x=F.grades i
    · have hh : wr F i=wr F x:= (congr_arg Prod.snd h).symm; rw [show (liftsC G k (rotate s k (P i))).2 0 r = 0 from ?_,smul_zero]; apply Auth.coverN (k:=wr F i) ?_ 0 r (by change wr F x<r at e; omega)
      change Auth _ (photo _); unfold P fetch; rw [Cloth.uprights,rises]; exact receipt _
    rw [show realM F s⁻¹ i x=0 from bleach_sparse F _ _ _ h,zero_smul] -- h

-- Each rotated upper-triangle projection preserves identity at weight-column grade.
private lemma units (s:Signed)(y:(L.level h).Index) (w:wr (L.level h) y=r)(x:TagIx (L.level h) r)
    (p:wT (L.level h) x ≤ wt (L.level h) y): row (L.level h) ((photo (Cloth.rotate s k (fetch H A R v y))).2 0 r) x= realM (L.level h) s x.val y:=by
    rcases x with ⟨x,hx⟩; obtain rfl:= (show wr (L.level h) x=r from hx)
    rw [Cloth.bangs H]; let r:=wr (L.level h) x; let P:=photo (elder A R L y)
    have hi (i:(L.level h).Index) (hq:wT (L.level h) (⟨i,rfl⟩:TagIx _ (wr (L.level h) i))≤ wt (L.level h) y) (v:wr (L.level h) y=wr (L.level h) i) : row (L.level h) (P.2 0 (wr (L.level h) i)) ⟨i,rfl⟩=if i=y then 1 else 0:=by
       have hb:= rung (A:=A) (R:=R) (⟨i,rfl⟩:TagIx (L.level h) (wr (L.level h) i)) ⟨y,v⟩ hq; simpa only [Subtype.mk.injEq] using hb
    rw [Finset.sum_eq_single y]; swap
    · intro j _ hj; by_cases H':(L.level h).grades x=(L.level h).grades j
      · have hu : wt (L.level h) j= wt (L.level h) x:= congr_arg Prod.fst H'.symm; unfold fetch; rw [rises,hi j (hu.trans_le p) (w.trans (congr_arg Prod.snd H')),if_neg hj,mul_zero]
      rw [show bleached (L.level h) s.ortho x j=0 from bleach_sparse _ _ _ _ (Ne.symm H'),zero_mul]
    swap; · simp
    unfold fetch; rw [rises,hi y le_rfl rfl,if_pos rfl,mul_one]
lemma account (x y:TagIx (L.level h) r)(p:wT (L.level h) x≤ wT (L.level h) y): row (L.level h) ((notesT (L:=L) H A R v y).photo.2 0 r) x= if x=y then 1 else 0:= by
    let F:=L.level h; let D:= fetch H A R v (L:=L); let U(s:Signed):=faux F D (fun s=> rotate s k) s y; let I:ℝ:= if x=y then 1 else 0; let a:ℝ:=(Fintype.card Signed:ℝ)⁻¹
    have ht (s): row F ((photo (U s)).2 0 r) x= I:=by
       let V(s:Signed)(i:F.Index):= rotate s k (D i); let Z i:= realM F s⁻¹ i y; have hb: photo (U s)= ∑ i, Z i • photo (V s i):=by unfold photo U faux; simp_rw [map_sum,map_smul]; rfl
       rw [hb, row_summed _ _ (fun i _=> receipt (V s i))]; have hv:= (realM_turn F s s⁻¹ x y).symm.trans (by rw [mul_inv_cancel, realM_id]; simp only [← Subtype.ext_iff]; rfl: _ = I)
       calc _ = ∑ i:F.Index,realM F s x i*realM F s⁻¹ i y:= Finset.sum_congr rfl (fun i _=>by
                 by_cases Q: F.grades y= F.grades i; · rw [show row F ((photo (V s i)).2 0 r) x= _ from units H A R v s i ((congr_arg Prod.snd Q.symm).trans y.property) x (p.trans_eq (congr_arg Prod.fst Q)),mul_comm] 
                 unfold Z; rw [show realM F s⁻¹ i ↑y=0 from bleach_sparse F _ _ _ Q,mul_zero,zero_mul])
            _ = I:= hv
    have hw : photo (notesT H A R v (L:=L) y)=∑ s:Signed, a • photo (U s):=by unfold photo notesT bandage; simp_rw [map_smul,map_sum,Finset.smul_sum]; rfl
    rw [hw,row_summed _ _ (fun j _=> receipt (U j))]; change ∑ s:Signed, a * row F ((photo (U s)).2 0 r) x=_; simp_rw [ht]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc, mul_inv_cancel₀ (by positivity),one_mul]

end podium
/-! The complete funded point palette (for any requested rank height k, makes sense for solving
all weights through h with h≤k). Uses top-only equations at that encounter, built into
exact Pill witnesses. `Nest` rather than using the Choice constructor through order later. -/
def Nest {L:Frames G}(H:Hol G)(A:∀ h, XSpace.Survey G H h)(R:∀ h,Rays G h H)(k:ℕ)(d:ℕ): Stove (L.level d) k:=if h:d≤k then notesT H A R h else 0
def launch (L:Frames G)(H:Hol G)(A:∀ h,XSpace.Survey G H h)(R:∀ h,Rays G h H)(k:ℕ) : TowerP L := fun d=> photo ∘ Nest H A R k d
section
variable (L:Frames G) (A:∀ h,XSpace.Survey G H h)(R:∀ h,Rays G h H)
lemma manifest (s:Signed)(p:h≤k): MotionP (L.level h) s (launch L H A R k h):=by rw [launch,Nest,dif_pos p]; exact envoy H A R p s
open Shard (Fruit)
lemma openRank (p:h≤k)(q:ℕ)(u:ℕ): ∃ B:ℝ, Palette (L.level h) (launch L H A R k h) k u q B:=by
    let F:=L.level h; let T:= notesT H A R p (L:=L)
    choose f hf using fun (i:F.Index)(b:Fin (q+1))(r:Fin (k+q+1))=> attends (receipt (T i)) b.val r.val u
    let F₀(x:F.Index × Fin (q+1) × Fin (k+q+1)):= f x.1 x.2.1 x.2.2; let B:= ∑ a,F₀ a; have hb (i):0≤ F₀ i:= (hf ..).C
    rw [launch,Nest,dif_pos p]
    refine ⟨B,⟨fun i=> receipt (T i), fun i v e=> posts_rank H A R p i e, fun i v r z=>?_, fun a i j p'=> account H A R p i j p'⟩⟩; change Fruit 0 1 u ((photo (T i)).2 v r) B; by_cases d:r≤ k+q
    · let x:= (i, (⟨v,by omega⟩: Fin (q+1)),(⟨r,by omega⟩: Fin (k+q+1))); exact (hf x.1 x.2.1 x.2.2).more (Finset.single_le_sum (f:=F₀) (fun _ _=>hb _) (Finset.mem_univ x))
    rw [(receipt _).coverN _ _ (by omega)]; exact Shard.Fruit.more Shard.Fruit.zero (Finset.sum_nonneg fun _ _=>hb _)
lemma unitedBill (h k q u:ℕ)(p:h≤k): ∃ B:ℝ,1≤B∧∀ X:ℝ,B≤X→∀ d,d≤h→Palette (L.level d) (launch L H A R k d) k u q X:=by
    choose V hv using fun a:Fin (h+1)=> openRank H L A R ((Nat.le_of_lt_succ a.isLt).trans p) q u
    let f a:=|V a|; let B:=∑ i,f i; have ht:0≤ B:= Finset.sum_nonneg fun _ _=>abs_nonneg _; refine ⟨1+B,by linarith,fun X hx i v=> (hv (⟨i,by omega⟩:Fin (h+1))).money ?_⟩; let a:Fin (h+1):=⟨i,by omega⟩; refine le_trans ((le_abs_self _).trans (Finset.single_le_sum (f:=f) (fun _ _=>abs_nonneg _) (Finset.mem_univ a))) ?_; change B≤X; linarith only [hx]
end
end YM.WilsonCoeffUV.Mer.Xa
