import YM.LocalLTE.XPhase.Rare
import YM.LocalLTE.Port.Gems
/-! # Filling real mixed K indices, never throwing away predicate requirements
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPhase
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof Accent GridApprox.Nil Extra.Trajectories Extra.Multi Planned.GuardedAtom Guard Overlay
open PhysicalNext.Repeat
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {w: V→ℝ} {t d s g e v y:ℝ} {N:ℕ}
variable [Fintype V] (B:Census V)(R:Rep G n) (lp:V)(K:Keeper R.p R.activities) (F:Box n→ Config G n→Poly B)
-- Use sparse slots. Aggregation by `barcode` for all support units.
variable (A:Bands B R)
abbrev cachet := Progress.DirectedRecipe.stuff (cart K) (fun i:StockTag n=>F i.val)
noncomputable def reserveIX (B : Census V):Rising B ↪ ℕ:=by let _ := Classical.choice (nonempty_encodable (Rising B)); exact ⟨Encodable.encode,Encodable.encode_injective⟩
local notation "Kp"=> cachet B R K F
local notation "κ"=> reserveIX B
open Progress.DirectedRecipe
-- stores K at slot.Kp era. reserve numbering tied to music.
noncomputable def shelve : Bands B R:= {A with units:=0,
                                                marks:=fun _=> Function.extend κ (fun i=>i.val) (fun _=>B.fire lp),
                                                entries:=fun i=> stuff κ (fun j U=> (cachet B R K F i U).part j.val) }
local notation "G'"=> shelve B R lp K F A
variable {o:V→Site n}(hf:∀ i,Flow A.origins i (F i) R.p.threshold)(hz:∀ i U,rises (F i U))
local notation "p"=> R.p
local notation "β"=> R.p.threshold
local notation "hh"=> R.activities
include hf hz
omit hz [Fintype V] in
lemma casks (i:ℕ) : Borne A.origins ((R.activities.forced i).support) (cachet B R K F i) β ∧ ∀ U,(cachet B R K F i U)≠0 → (hh|>.forced i).eligible β U:=by
    by_cases he:i∈Set.range (cart K);swap
    · rw [cachet,blank _ _ he]; exact ⟨⟨fun _ _ _ _=> rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun i ht=>(ht rfl).elim⟩
    obtain ⟨i,rfl⟩:=he; let b:=i.val
    have hp: (hh|>.forced (_root_.YM.MergeProof.cart K i)).support=b.1:= congr_arg Prod.fst (cardK K i)
    rw [cachet,stuffed,hp]; refine ⟨(hf b).toBorne,fun U hu=>?_⟩
    have hx : (hh|>.forced (cart K i)).support ∩ flags β U=(hh|>.forced (cart K i)).inventory:=by rw [hp]; exact ((hf b|>.permits U hu).1.trans (congr_arg Prod.snd (cardK K i)).symm)
    exact ⟨hx,K.pass _ U hx⟩
omit hf [Fintype V] in
lemma rears (i:ℕ)(U:Config G n): rises (cachet B R K F i U):=by by_cases hi:i∈Set.range (cart K); obtain ⟨i,rfl⟩:=hi; rw [cachet,stuffed];exact hz _ _; rw [cachet,blank _ _ hi]; exact fun i h=> False.elim (h rfl)
omit hz [Fintype V] in
lemma roomH (hZ:A.Active): (G').Active∧(∀ i j,(G').entries i j≠0→2 ≤ ((G').marks i j).val.card):=by
    let f(i:ℕ):= cachet B R K F i; have hp := casks B R K F A hf
    let m(i:ℕ):= (G').marks 0 i; let s := κ
    have hY(i):m (s i)=i.val:= (s.injective.extend_apply (fun z=>z.val) (fun _=>B.fire lp) i)
    refine ⟨⟨hZ.proper,hZ.pins,hZ.regular,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · intro i j; change (m j|>.val).Nonempty; by_cases h:j∈Set.range s; obtain ⟨j,rfl⟩:=h; rw [show m (s j)= _ from hY j]; exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) j.property)
      rw [show m j=B.fire lp from Function.extend_apply' (fun v:Rising B=>v.val) (fun _=>B.fire lp) j h]; exact Finset.singleton_nonempty _
    all_goals intro i j
    all_goals by_cases hx:j∈Set.range (reserveIX B)
    all_goals first | rw [show (G').entries i j=0 from blank κ (fun j U=>(cachet B R K F i U).part j.val) hx] | obtain ⟨j,rfl⟩:=hx; rw [show (G').entries i _= _ from (show (G').entries i (κ j)=(fun U=>(f i U).part j.val) from stuffed κ (fun j U=>(cachet B R K F i U).part j.val) j)]
    -- 12
    · intro hl; obtain ⟨V,hV⟩:= Function.ne_iff.mp hl; change (f i V).part _≠0 at hV
      change ∀ z∈(m (s j)).val,_; rw [hY j]; intro z hz; by_contra hy; exact hV ((hp i).1.scope _ _ (fun hX=> hy (hX hz)))
    · intro h; exact (h rfl).elim
    · intro U V hU h'; exact congr_arg (fun q:Poly B=>q.part j.val) ((hp i).1.home U V hU h')
    · exact fun _ _ _ _=>rfl
    · intro U hu; exact (hp i).2 _ fun h=>hu (by change (cachet B R K F i U).part _=0;rw [h]; exact rfl)
    · exact fun _ h=>(h rfl).elim
    · exact (hp i).1.me j.val
    · exact measurable_const
    · exact fun g' U=>congr_arg (fun q:Poly B=>q.part j.val) ((hp i).1.turns g' U)
    · exact fun _ _=>rfl
    · intro hH; change 2≤(m (s j)).val.card; rw [hY]; exact j.property
    · intro h; exact (h rfl).elim
omit hf hz
omit [Fintype V] in
lemma tagged_b (i:ℕ)(j:Rising B) : (G').marks i (reserveIX B j)=j.val∧ (G').entries i (reserveIX B j)=(fun U=>(cachet B R K F i U).part j.val):=by
    unfold shelve; dsimp only; exact ⟨Injective.extend_apply (reserveIX B).injective (fun i=> i.val) (fun _=>B.fire lp) j, stuffed (reserveIX B) (fun k U=> (cachet B R K F i U).part k.val) _ ⟩
omit [Fintype V] in
lemma tagged_v (i j:ℕ)(h:j∉Set.range (reserveIX B)) : (G').entries i j=0:=blank κ (fun j U=>(cachet B R K F i U).part j.val) h
abbrev lightF := fun q:Box n=>fun (U:Config G n)=>∑' i : {i // barcode R.activities i=q},∑' j,A.tagged i.val j U
-- phi.Mask.Part switches all T.Older.
include hf hz
local notation "e'"=> reserveIX B
local notation "Λ"=>cachet B R K F
omit [Fintype V] in
lemma blazing : lightF B R (G') = F:=by
    funext i U; have hv(j): (∑' k, (G').tagged j k U)= Λ j U:=by
       let f:= (Λ j U); let g(i:Rising B):= Poly.send i.val (f.part i.val)
       have hp:=tagged_b B R lp K F A j
       refine (transferred_sum (reserveIX B) (fun l=> (show (G').tagged j (reserveIX B l) U=g l from ?_)) (fun i hi=> (show (G').tagged j i U=0 from ?_))).trans ?_
       · unfold Bands.tagged; rw [(hp l).1,(hp l).2]; try rfl
       · unfold Bands.tagged; rw [tagged_v B R lp K F A j i hi]; exact Poly.send_zero _
       rw [tsum_fintype]; have h : rises f:= rears _ _ _ _ hz _ _
       let V(_:Unit)(_:Config G n): Poly B:=f
       have hy:= XPhase.packed V (U:=U) (fun _=>h)
       simpa only [g,Fintype.sum_prod_type,Fintype.sum_unique] using! hy
    unfold lightF; simp_rw [hv]; by_cases h : Sure i
    · let y : Extra.Histories.StockTag n := ⟨i,h⟩; let j:= cart K y; let Aι : {x // barcode R.activities x=i}:=⟨j,cardK K y⟩
      rw [tsum_eq_single Aι]; rw [cachet,show Aι.val=cart K y from rfl,stuffed]
      intro t h'; rw [cachet,blank _ _ ?_];rfl; rintro ⟨b,hb⟩; apply h'; apply Subtype.ext; have hp:b.val=i:=(cardK K b).symm.trans ((congr_arg (barcode R.activities) hb).trans t.property); exact hb.symm.trans (congr_arg _ (show b=y from Subtype.ext hp))
    haveI:IsEmpty {j // barcode R.activities j=i}:= ⟨by rintro ⟨j,hj⟩; subst i; exact h ⟨(R.activities.forced j).inventory_ne,(R.activities.forced j).inventory_sup⟩⟩
    rw [tsum_empty, not_not.mp (mt ((hf i).permits U) (fun hc=>h hc.2))]
variable (hq:∀ i,0<w i)(hp:Towed w Prod.fst F R.p.B R.p.supportExponent s)
open Push.AbsoluteSums
include hp hq
-- Div costs transcribed.
omit hz in
lemma carved : ∃ f: ℕ×ℕ→ℝ,(∀ i j,0 ≤ f (i,j)∧∀ U, ‖(shelve B R lp K F A).entries i j U‖ ≤ f (i,j))∧∀ i:V,SumBudget (fun (k:ℕ×ℕ)=> if i∈ ((G').marks k.fst k.snd).val then Poly.toll w ((G').marks k.fst k.snd)*R.p.mass (R.activities.forced k.fst).support (f k) else 0) s:=by
    obtain ⟨a,ha,hA,h⟩:=hp; choose φ hv hV hT using h
    let u : StockTag n × Rising B ↪ ℕ × ℕ:= (cart K).prodMap e'
    let g0 (i:Box n× Rising B):= if i.2.val.val.image A.origins ⊆ i.1.1 then φ i.1 i.2.val else 0
    let g(i: StockTag n× Rising B):=g0 (i.1.val,i.2); let f:= stuff u g; have hVt(i):0≤ g0 i:=by unfold g0;split;exact hv _ _; rfl
    refine ⟨f,fun i j=> ?_,fun k=> ?_⟩
    · by_cases hp:(i,j)∈ Set.range u; swap
      · rw [show f (i,j)=0 from blank _ _ hp]; refine ⟨le_rfl,fun V=>?_⟩;by_cases h:j∈Set.range e';swap; · rw [tagged_v _ _ _ _ _ _ i j h]; simp
        obtain ⟨j,rfl⟩:=h
        rw [tagged_b B R lp K F A i j|>.2]; dsimp only; unfold cachet; rw [blank _ _ ?_]; simp only [Pi.zero_apply,Poly.part_nil,norm_zero]; rfl
        rintro ⟨p',hP'⟩; exact hp ⟨(p',j),Prod.ext hP' rfl⟩
      obtain ⟨⟨i',j'⟩,ht⟩:=hp; have hI : cart K i'=i:= congr_arg Prod.fst ht; have ht':e' j'=j:=congr_arg Prod.snd ht; subst i j
      rw [← ht,show f (u (i',j'))=_ from stuffed u g (i',j')]; refine ⟨hVt _,fun V=>?_⟩
      rw [tagged_b B R lp K F A _ j' |>.2]; dsimp only; rw [cachet,stuffed]; unfold g; dsimp only; unfold g0; split; exact hV _ _ _; next hn=>rw [show (F i'.val V).part _= 0 from Classical.byContradiction (fun h=> hn ((hf i'.val).toBorne.place _ _ h)),norm_zero]
    let v0(i:Box n × Rising B):= if k∈ i.2.val.val then Poly.toll w i.2.val * R.p.mass i.1.1 (g0 i) else 0
    let v (i:StockTag n × Rising B):= v0 (i.1.val,i.2)
    have hv0(i):0≤ v0 i:=by unfold v0; split; exact mul_nonneg ((Poly.worth hq _).le) (mul_nonneg (Real.exp_nonneg _) (hVt _)); rfl
    have hθ : SumBudget v s := by
       let e: StockTag n × Rising B ↪ Box n× Rising B:= (show StockTag n ↪ Box n from ⟨Subtype.val,Subtype.val_injective⟩).prodMap (.refl _)
       apply budget_pull e e.injective (w:=v0)
       refine ⟨hv0,Summable.of_finite,?_⟩
       have h := (hA (A.origins k)).2.2; rw [tsum_fintype] at h; rw [tsum_fintype,Fintype.sum_prod_type]; refine le_trans (Finset.sum_le_sum (fun i hi=> ?_)) h
       by_cases hx:A.origins k∈i.1
       · rw [if_pos hx]; apply le_trans _ (mul_le_mul_of_nonneg_right (hT i) (Real.exp_nonneg _)); rw [wordsPrice,Finset.sum_mul]
         let c(j:B.Mode):= Poly.toll w j * (φ i j) * Real.exp (R.p.supportExponent *coverNumber R.p.B i.1)
         have hz: (∑ x:Rising B,c x.val)≤∑ j:B.Mode,c j:=by
             let e:= fun i:Rising B=>i.val; rw [← show ∑ i∈ Finset.univ.image e,c i= _ from Finset.sum_image (Subtype.val_injective.injOn)]; exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _=>mul_nonneg (mul_nonneg ((Poly.worth hq _|>.le)) (hv _ _)) (Real.exp_nonneg _))
         refine le_trans (Finset.sum_le_sum (fun j hj=>?_)) hz; unfold v0; split
         next h=>
            unfold c BudgetPoint.mass g0; dsimp only; split
            next h'=> exact le_of_eq (by ring)
            next h'=> simp only [mul_zero]; exact mul_nonneg (mul_nonneg ((Poly.worth hq _).le) (hv _ _)) (Real.exp_nonneg _)
         next h=> exact mul_nonneg (mul_nonneg (Poly.worth hq _|>.le) (hv _ _)) (Real.exp_nonneg _)
       rw [if_neg (show A.origins k∉ Prod.fst i from hx),sum_eq_zero]
       intro j h; unfold v0; dsimp only;split
       next hk=> rw [show g0 (i,j) = 0 from if_neg (fun h=>hx (h (Finset.mem_image_of_mem _ hk)))]; simp [RG.BudgetPoint.mass]
       next h=> rfl
    refine transfer_budget u ?_ ?_ hθ
    · rintro ⟨i,j⟩; change (if k∈ ((G').marks _ (e' j)).val then _ else 0) = _; rw [tagged_b _ _ _ _ _ _ _ j|>.1]; split
      next h=>
        change Marker.Poly.toll w _*R.p.mass (R.activities.forced (cart K i)).support _= _
        rw [show f (u _) = _ from stuffed u g (i,j), show (R.activities.forced _).support=i.val.1 from congr_arg Prod.fst (cardK K i),show (shelve B R lp K F A).marks (u (i,j)).1 (u (i,j)).2=j.val from tagged_b B R lp K F A _ j|>.1]; exact (if_pos (show k∈ j.val.val from h)).symm
      next hh1=> exact (if_neg (show k∉j.val.val from hh1)).symm
    intro i hh1; split
    · rw [show f _=0 from blank _ _ hh1,BudgetPoint.mass,mul_zero,mul_zero]
    rfl
end YM.LocalLTE.XPhase
