import YM.Frontier6.Multi.Comparable.Solo

/-! Payroll primary at orientation, actual extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T:Fareway I}
variable (K: Final C H S){ξ:Ultrafilter (ℕ×ℕ)}{j k m:I→ℕ} (hξ:ξ.toFilter≤ H.fuse) (hc:Extraction.Wcmain C){a b c ε:ℝ}
variable (d:ℕ)
variable {O:Type}[Fintype O][DecidableEq O]

namespace Plan
variable {i p q : ℕ} (z:O→ Cover)(t:O→ℕ)(v:(i:O)→ C.label (t i)) (u:C.label d)
abbrev Fault (O:Type) : Bool→ Type:= fun i=> Bool.rec O Unit i
instance switchO (b:Bool): Fintype (Fault O b):= Bool.rec (motive:=fun b=> Fintype (Fault O b)) inferInstance inferInstance b

def trouble : Plan C Bool (Fault O) where
   point b:= Bool.rec (motive:=fun b=> Fault O b → Cover) z (fun _=>0) b
   letter b:= Bool.rec (motive:=fun b=> Fault O b → C.book.Token) (fun i=>⟨t i,v i⟩) (fun _=>⟨d,u⟩) b
   fee b:= if b then -1 else 1
lemma trouble_same : (trouble d z t v u).cost i p q=leafGap C i d t z v p q u:=by
    funext U; let Y:= trouble d z t v u; unfold cost; rw [Fintype.sum_bool]
    let W:= C.O p q u 0 U
    have he : (∏ j:Fault O true,C.O p q (Y.letter true j).2 (location C.S i p q (Y.point true j)) U)=W:=by
       change (∏ j:Unit,C.O p q u (location C.S i p q 0) U)=_; simp [W,location_origin]
    change -(1:ℂ)*(∏ j:Fault O true,C.O p q _ _ U)+1*(∏ j:O,C.O p q (v j) _ U)= _
    rw [he]; unfold leafGap leaves; simp only [Pi.sub_apply, Finset.prod_apply]; change -(1:ℂ)*W+1*(∏ i',C.O p q (v i') (location C.S i p q (z i')) U)= _ - W; ring

lemma trouble_point {S:Table C.book}(s:E4) : (trouble d z t v u).syntaxR i s S=assembly S (fun x=> C.S.gridPoint i (z x)+s) (fun i=>S.classTokens (⟨t i,v i⟩:C.book.Token))-Tale.letter S s ⟨d,S.project _ u⟩:=by
   unfold syntaxR; rw [Fintype.sum_bool]
   let n:=fun j:Unit=>(⟨d,S.project _ u⟩:S.Tag)
   have hX: assembly S (fun _: Unit=> C.S.gridPoint i 0+s) n=Tale.letter S s ⟨d,S.project _ u⟩:= by
       unfold assembly; rw [Fintype.prod_unique]; rw [show C.S.gridPoint i 0=0 from (by ext; simp [Schedule.gridPoint])]; change Tale.letter S (0+s) _=_; rw [zero_add]
   change (-1:ℂ) • assembly S (fun _:Unit=>C.S.gridPoint i 0+s) n+1 • assembly S _ _= _
   rw [hX,one_smul,neg_one_smul,add_comm, sub_eq_add_neg]; rfl
end Plan

open PhysicalNext.Repeat.Legato Canvas Next.Extract Dash
section
variable {T':Table C.book}{L:ℕ→Table C.book}{R:Bin T'}{Y:DiffPlan S} (h:Base C H T' L R S Y) (h':Realm C)(hG:G.Simple) (hx:Bench C.S T j c)(hm:Bench C.S T m a)(hk:Bench C.S T k b)
set_option quotPrecheck false
variable (t:O→ℕ)(p:(i:O)→C.label (t i))(z:I→O→ Cover)
local notation "A"=>fun i:I=> C.S.gridPoint (j i) ∘ z i
local notation "ψ"=>forestPower t a c ε
local notation "U"=> fun k:O=> S.classTokens (⟨t k,p k⟩:C.book.Token)
-- terse 
include h h' hG hx hm hk hξ hc
lemma credit (root:O)(he:a<1)(hq:1<c)(hp:0 < b) (hz:b<a)(hw:0 < ε)(ht:Aspect T (fun i=> C.S.gridPoint (j i) ∘ z i))(hA':∀ᶠ i in T.via,∀ a:Axis, Injective (fun b=> (C.S.gridPoint (j i) (z i b)) a)) :
    ∃ v:I→ S.Field d,
    (∀ b:Fin (d+1), T.Costs (fun i=> weight K b (Tale.reach K d b (v i))) (ψ-(b.val:ℝ)*a)) ∧
    Permit K T ξ j k (fun i x=> assembly S (fun u=> (C.S.gridPoint (j i) (z i u))+x) U -letter S x ⟨d,v i⟩) (-(welcome t d a c b ε)):=by
   let v'(i):= (C.labels.level (t i)).coeffSize (p i)+1; have hs i:0 < v' i:= lt_of_le_of_lt (Work.G08.size_nonneg ..) (lt_add_one _)
   obtain ⟨B,M,hX,hY,hM,hN⟩:= scenery C hG t d p H hx hm hk z h.family hw he hq h' hz hp ht v' root hs (fun i=> (lt_add_one _).le)
   let f i (Z:C.label d) := ReferenceFit K Z (m i) (B i) ∧ Centered C ξ (k i) (fun j'=> leafGap C (j i) d t (z i) p j'.1 j'.2 Z) (2*M i)
   have hXc : ∀ᶠ i in T.via, ∃ x, f i x:=by
       filter_upwards [hN,hk.infinite.eventually_ge_atTop (C.ref d), hk.later hm hz] with i hi hk hv; exact related p h K h' hG hc ξ hξ _ hk hv.le hi (by linarith only [hM i])
   let q(i):C.label d:= if h:∃ x,f i x then h.choose else 0
   have hC:∀ᶠ i in T.via,f i (q i):= hXc.mono (fun i hi=> by unfold q; rw [dif_pos hi]; exact hi.choose_spec)
   let Z i:= S.project _ (q i)
   let G(i):= Plan.trouble d (z i) t p (q i)
   refine ⟨Z, fun y=>?_, Bool,inferInstance,Plan.Fault O, inferInstance,G, (fun i=>2*M i), ?_,?_,?_⟩
   · let V(b:S.Field d):= weight K y (reach K d y b); have hg(y:Fin (d+1)): y.val ≤ d:= by omega
     let T':= weight K y ∘L reach K d y ∘L LinearMap.toContinuousLinearMap (S.project d)
     let F :=fun i=> voyage C d (m i) (d-y) * B i; have hf:T.Mint F (ψ-(y:ℝ)*a):= ((hm.notes (voyage_pitch C d _)).mul hX).eq (by rw [Nat.cast_sub (hg y)]; ring)
     refine Costs.allows_norm (f:=fun i=> T' (q i)) (z:=fun i=>‖T'‖*F i) ?_ (hC.mono (fun i hi=> ?_))
     · simpa only [zero_add] using (Costs.const ‖T'‖|>.mul hf.pay)
     exact floors K _ (hg y) (q i) _ hi.1
   · intro b p; cases b with
     | true=> convert! (Costs.free (T:=T) (a:=-1) (X:= E4)) using 2; ext;simp [G,Schedule.gridPoint,Plan.trouble]
     | false=> exact ht.1 p
   · simpa only [zero_add] using ((T.minted_c _ zero_lt_two).pay.mul hY)
   filter_upwards [hC,hA'] with i hi hx; refine ⟨fun b a=> ?_, mul_nonneg zero_le_two (hM i).le, ?_,fun p=>?_⟩
   · cases b; exact hx _; exact fun _ _ _=> rfl
   · unfold G; simp_rw [Plan.trouble_same]; exact hi.2
   unfold G; rw [Plan.trouble_point]; exact Tale.almost K _
end
end YM.Frontier6.Road
