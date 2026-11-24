import YM.FormalBulk08.Sable.Bushel

/-! Exact slot cancellations witnessed without polynomial presentations of addresses. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {I:Type} {o:Loc G 1}{u m n d D r e:ℕ} {η A B :ℝ} {F: Frame G d}

def Steam (T:Tile (edgeL G) m)(u:ℕ)(B:ℝ)(o:Loc G 1) :=∀ k:ℕ,∀ h:m=k+1, Knoxville (grain (fame _) 1) u (0,o) (tap (lengthen h T)) B
lemma steam_m {T:Tile (edgeL G) m}(h:Steam T u A o)(he:A≤B):Steam T u B o:= fun i hi=>(h i hi).mono he
lemma roofSte {T:Tile (edgeL G) (m+1)}(h:Knoxville (grain (fame _) 1) u (0,o) (tap T) B): Steam T u B o:= fun p hp=>by cases Nat.add_right_cancel hp;exact h
lemma circuit (a:Loc G 1)(V:Fin m→edgeL G→ℝ)(h:∀ i,Footing (V i) d)(i:Fin m)(f:E4→ G.Color)(ht:f∈rangeLt G.Color (n+1))(hk:n+1≤d)(he:d*d≤u)(hm:m≤d)(e:V i=assigns (jump f)) :∃ C:ℝ,0≤C ∧∀ T:Tile (edgeL G) m, Agate T→ (∃ A B η, 0<η ∧ Knoxville (fame _) η (0,a) T A ∧ Torrid T η B a) →∀ B:ℝ, Steam T u B a→ ‖tariffs V T‖≤C*B:= by
   cases m with
   | zero=> exact Fin.elim0 i
   | succ m=>
     let s:=Equiv.swap (0 : Fin (m+1)) i; let K:= V ∘ s; let W:Fin (m+1)→edgeL G→ℝ:=update K 0 (patcher f)
     have hW j:Footing (W j) d:= by
        by_cases hx:j=0; rw [show W j = patcher f from hx.symm ▸ update_self ..]; exact tread_m (shoe_patch f ht) hk
        unfold W;rw [update_of_ne hx]; exact h _
     obtain ⟨C,hC,H⟩:=weave W a hW ((Nat.mul_le_mul_right d hm).trans he); refine ⟨C,hC,fun T ht' hp B hu=>?_⟩
     obtain ⟨Z,Z',η,hs,hS,hT⟩:=hp
     have hh : tariffs K T=tariffs W (tap T):=by
        rw [press_merit K a T hS hs (fun j=> foot_stip (h _)),press_merit W a (tap T) (current.mp hT) hs (fun j=>foot_stip (hW _))]; apply tsum_congr; intro p; rw [show W 0=patcher f from update_self .., show K 0=assigns (jump f) by simp [K,s,e],fade f ht p T hs hS (current.mp hT)]; congr 1
     rw [←tariff_turn V T ht' s]; unfold K at hh; rw [hh]; exact H (tap T) B (hu m rfl)

lemma midcast (a:Loc G 1)(F:Frame G d)(n k:ℕ)(w:Fin n→ℕ)(U:Fin n→Place.Potential G)
    (hv:∀ i,U i∈rangeLt (Axis→G.Color) (w i)) (hp:k≤d+1)(h:n≤d)(hu:∑ i,w i<k)(hs:(d+1)*(d+1)≤u):∃ C:ℝ,0≤C ∧ ∀ T:Tile (edgeL G) n,Agate T→Monic (slate T d n) → (∃ A B η, 0<η ∧ Knoxville (fame _) η (0,a) T A ∧ Torrid T η B a)→ ∀ A:ℝ,0≤A → Steam T u A a → (∀ i:F.Index,(F.grades i).1<k→(F.grades i).2=n → ‖pearlJ F T i‖≤ A) → ‖tariffs (fun i=> assigns (U i)) T‖≤ C*A:= by
   have hh i:w i≤d:= by have ht:=Finset.single_le_sum (f:=w) (fun j _=>Nat.zero_le _) (Finset.mem_univ i); omega
   choose f X hf hx H using fun i=>generated (U i) (hv i) (hh i)
   let V (i:Fin n) (b:Bool) := if b then assigns (jump (f i)) else assigns (Place.sampled (X i))
   have he i b: Footing (V i b) (d+1):= by unfold V; split; exact tread_m (jump_f _ (hf i)) ((hh i).trans (by omega)); exact turf_f (stead (X i))
   have hz (b: Fin n→Bool) : ∃ C:ℝ,0≤C ∧ ∀ T:Tile (edgeL G) n,Agate T→Monic (slate T d n) → (∃ A B η, 0<η ∧ Knoxville (fame _) η (0,a) T A ∧ Torrid T η B a)→ ∀ A:ℝ, Steam T u A a → (∀ i:F.Index,(F.grades i).1<k→(F.grades i).2=n → ‖pearlJ F T i‖≤ A) → ‖tariffs (fun i=> V i (b i)) T‖≤ C*A := by
      by_cases h' :∀ i,b i=false
      · obtain ⟨C,hC,H⟩:=diagram F k X w hu hp hx h; refine ⟨_,hC,fun T he ht hV A hT hA=>?_⟩; obtain ⟨B,C,η,h,hV,-⟩:=hV; simp_rw [h']; rw [show (fun i=>V i false)=(fun i=> assigns (Place.sampled (X i))) from rfl,←severance T he hV h]; exact H (slate T d n) ht _ (fun i hj hi=> by have he:=hA i hj hi; unfold pearlJ at he; rw [hi] at he; exact he)
      push Not at h'; obtain ⟨i,hi⟩:=h'; obtain ⟨C,hC,J⟩:= circuit a (fun i=> V i (b i)) (fun i=> he i _) i (f i) (hf i) ((Nat.add_le_add_right (hh i) _)) hs (by omega) (by simp [V,Bool.eq_true_of_not_eq_false hi])
      exact ⟨_,hC,fun T hp _ ht A hx _=> J T hp ht A hx⟩
   choose C hC hD using hz; refine ⟨∑ i,C i,Finset.sum_nonneg (fun i _=>hC i),fun T ht hT hv A hA hx hV=>?_⟩
   obtain ⟨B,D,η,hs,hb,hp⟩:=hv
   rw [show (fun i=>assigns (U i))=fun i=> ∑ u:Bool,V i u by funext i; rw [H i,Fintype.sum_bool];rfl,dial V (fun i b=>foot_stip (he i b)) hs T hb, Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> hD i T ht hT ⟨_,_,_,hs,hb,hp⟩ A hx hV)
-- analytic SOME for receipts WITH tap.
lemma ferry (Y: Anthem D G)(h:Clef o Y r)(p:Dawn.Studio D)(e m:ℕ):∃ A B η, 0<η ∧ Knoxville (fame _) η (0,o) (Y p e m) A ∧ Torrid (Y p e m) η B o:= by
   let S:Finset (ℕ×ℕ):=(Finset.range (e+1)) ×ˢ Finset.range (m+1)
   choose X C hX hC HX using h.fare.2.2
   let f (v:ℕ×ℕ):= X v.1 v.2; let b(v:ℕ×ℕ):= C v.1 v.2*‖p‖
   have hb v:0≤b v:=mul_nonneg (hC ..) (norm_nonneg _)
   have he : (e,m)∈S:= by simp [S]
   obtain ⟨i,hi,h⟩:= Finset.exists_min_image S f ⟨_,he⟩; let M:=∑ v ∈S,b v; have hm:0≤M:= Finset.sum_nonneg (fun i _=>hb i); let η:= f i/4; have hz:2*η<f i:= by unfold η; have hh:= (show 0< f i from hX _ _);linarith
   have he':0<η :=div_pos (hX ..) (by norm_num)
   have hh (j l:ℕ)(ht:(j,l)∈ S): Knoxville (fame _) (f i) (0,o) (Y p j l) M:= by refine (penn_shrink (HX j l p) (h _ ht)).mono (Finset.single_le_sum (f:=b) (fun x _=>hb x) ht)
   cases m with
   | zero=> exact ⟨_,0,_,he', (penn_shrink (hh e 0 he) (show η ≤ f i by linarith)), fun i hi=>by omega⟩
   | succ m=>
      have hr:= (show Clef o Y r from ‹Clef o Y r›)
      obtain ⟨K,hK,H⟩:=marker_print o e m hz he'.le; refine ⟨M,K*M,η,he',penn_shrink (hh e _ he) (show η ≤ f i by linarith),?_⟩; exact current.mpr (H _ (shells Y hr p) (hr.fare.2.1 p _ _) _ hm (fun j hv l _ he=> hh j l (by simp only [S, Finset.mem_product,Finset.mem_range]; omega)))

def Steps (F: Labels.Frame G d) (a: Loc G 1)(u q e r:ℕ)(Y: Anthem D G)(B:ℝ):Prop:= 0≤B ∧ (∀ v,Steam (Y v e r) u (B*‖v‖) a) ∧∀ v:Letter F, Pose.slots F v=r→Pose.weight F v<q→ ‖pearlJ F (Y (inside F v D) e r) (mint F v)‖≤ B
lemma stitchK (a: Loc G 1)(F:Frame G d)(h q n:ℕ)(he:q≤d+1)(s:Dawn.Seasons)(D l:ℕ)(U: Fin n →Place.Potential G)(r:Fin n→ℕ)(hr:∀ i,0<r i)(hp:(∑ i,r i)+Chapel.upper s<q)(hw:∀ i,U i∈rangeLt (Axis→G.Color) (r i))(H:Source.Hol G)(hs:(d+1)*(d+1)≤u):∃ C:ℝ,0≤C ∧∀ Y:Anthem D G, Clef a Y l→∀ B:ℝ, Steps F a u q h n Y B → ‖tariffs (fun j=> assigns (U j)) (Y (Dawn.cone D s) h n)‖≤ C*B:= by
    obtain he' :=(Cases.arity hr).trans (show (∑ i,r i)≤ d by omega)
    let p:= Dawn.cone D s; let c:= q-Chapel.upper s
    obtain ⟨C,hC,hQ⟩:= midcast a F n c r U hw (by omega) he' (by unfold c;omega) hs
    let d':=max 1 ‖p‖; have hd: 1≤ d':= le_max_left ..
    refine ⟨C*d',mul_nonneg hC (zero_le_one.trans hd),fun Y hY B hB=>?_⟩
    obtain ⟨Z,A,η,hp',hz,ht⟩:=ferry Y hY p h n
    let T:= Y p h n; have hl: Monic (slate T d n) := monic_slate a T H hp' hz (perfumed Y hY p h n) _ _
    rw [mul_assoc]; refine hQ T (hY.fare.2.1 p h n) hl ⟨_,_,_,hp',hz,ht⟩ _ (mul_nonneg (zero_le_one.trans hd) hB.1) (steam_m (hB.2.1 p) ?_) (fun i hi hx=>?_)
    · rw [mul_comm _ B]; exact mul_le_mul_of_nonneg_left (le_max_right ..) hB.1
    have hk : Chapel.upper s≤d:= by omega
    let j: Letter F := ⟨(i,(⟨s,(Dawn.paper_is _).mpr hk⟩:Dawn.Spring d)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (F.grades i).1+Chapel.upper s≤d from (by unfold c at hi;omega)⟩⟩
    have hz : Pose.weight F j<q:= by change (F.grades i).1+ Chapel.upper s< q; unfold c at hi; omega
    exact (hB.2.2 j hx hz).trans (le_mul_of_one_le_left hB.1 hd)
end YM.FormalBulk08.Sable
