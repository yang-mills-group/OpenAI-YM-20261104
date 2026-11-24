import YM.FormalBulk08.Grail.Bar

/-! Zero-component tests suffice to price polynomial interpolation including
low polynomiality absent on transverse gauge representatives. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{l n d m :ℕ}{A B η θ : ℝ}{o:Loc G 1}
variable {I : Type*}{F : Frame G d}

def Torrid (T:Tile (edgeL G) m) (η B:ℝ)(o:Loc G 1):=∀ r:ℕ,∀ h:m=r+1, Knoxville (fame _) η (0,o) (tap (lengthen h T)) B
lemma current {T:Tile (edgeL G) (m+1)} : Torrid T η B o ↔ Knoxville (fame _) η (0,o) (tap T) B:= ⟨fun h=>h _ rfl,fun h r e=>by cases Nat.add_right_cancel e;exact h⟩
lemma torrid_mono {T:Tile (edgeL G) m} (h:Torrid T η A o)(he:A≤B): Torrid T η B o:=fun i hi=>(h i hi).mono he

lemma sharp_decay (o:Loc G 1)(u:Fin m→edgeL G→ℝ)(hp:∀ j, Stipend (u j))(i:Fin m)(f:E4→ G.Color)(ht:f∈rangeLt G.Color (n+1))(e : u i= assigns (jump f))(hs:0<η): ∃ C:ℝ, 0≤C∧∀ T:Tile (edgeL G) m, Agate T→ ∀ A B:ℝ, Knoxville (fame _) η (0,o) T A→ Torrid T η B o→ ‖tariffs u T‖≤ C*B:= by
   cases m with
   | zero=> exact Fin.elim0 i
   | succ m=>
     let s:=Equiv.swap (0 : Fin (m+1)) i; let K:= u∘s
     let W : Fin (m+1)→edgeL G→ℝ := update K 0 (patcher f)
     have hW j: Stipend (W j):= by by_cases hx:j=0; rw [show W j = patcher f from hx.symm ▸ update_self ..]; exact patcher_pay f ht
                                   unfold W; rw [update_of_ne hx];exact hp _
     obtain ⟨C,hC,H⟩:=pays_product W o hs hW; refine ⟨C,hC,fun T hf A B hS hT=>?_⟩
     have hT :=hT m rfl
     have hh: tariffs K T=tariffs W (tap T) := by
        rw [press_merit K o T hS hs (fun j=>hp _),press_merit W o (tap T) hT hs hW]; apply tsum_congr; intro p; rw [show W 0=patcher f from update_self .., show K 0=assigns (jump f) by simp [K,s,e], fade f ht p T hs hS hT]; congr 1
     rw [←tariff_turn u T hf s]; unfold K at hh; rw [hh]; exact (H (tap T) B hT).2
lemma dial {J : Fin m→ Type*} [∀ i,Fintype (J i)] (S:∀ i, J i→edgeL G→ℝ)(h:∀ i j, Stipend (S i j))(hs:0<η)(T:Tile (edgeL G) m)(ht: Knoxville (fame _) η (0,o) T A): tariffs (fun i=>∑ u:J i,S i u) T=∑ s:(i : Fin m)→ J i,tariffs (fun i=> S i (s i)) T:= by
    unfold tariffs; simp_rw [Finset.sum_apply,Fintype.prod_sum,Finset.mul_sum]; rw [Summable.tsum_finsetSum]; intro a _; exact ((pays_product (fun j=> S j (a j)) o hs (fun i=> h i _)).choose_spec.2 T A ht).1
lemma radar (a:Loc G 1)(F:Frame G d)(n k:ℕ)(w:Fin n→ℕ)(U:Fin n→Place.Potential G)
    (hv:∀ i,U i∈rangeLt (Axis→G.Color) (w i)) (hp: k≤d+1)(h:n ≤ d)(hu:∑ i,w i<k)(hs:0<η) :∃ C:ℝ,0≤C ∧∀ T:Tile (edgeL G) n,Agate T →Monic (slate T d n) → ∀ A B:ℝ,0≤A → Knoxville (fame _) η (0,a) T B → Torrid T η A a → (∀ i:F.Index,(F.grades i).1< k→(F.grades i).2=n → ‖pearlJ F T i‖≤ A) → ‖tariffs (fun i=> assigns (U i)) T‖ ≤ C*A:= by
   have hh i:w i≤d:= by have ht:=Finset.single_le_sum (f:=w) (fun j _=>Nat.zero_le _) (Finset.mem_univ i); omega
   choose f X hf hx H using fun i=>generated (U i) (hv i) (hh i)
   let V(i:Fin n)(b:Bool) := if b then assigns (jump (f i)) else assigns (Place.sampled (X i))
   have he i b: Stipend (V i b):= by unfold V;split; exacts [jump_pay _ (hf i),shoulder (stead (X i))]
   have hz (b : Fin n→Bool):∃ C:ℝ,0≤C ∧∀ T:Tile (edgeL G) n, Agate T→Monic (slate T d n) →∀ A B:ℝ, Knoxville (fame _) η (0,a) T B →Torrid T η A a → (∀ i:F.Index,(F.grades i).1<k→(F.grades i).2=n →‖pearlJ F T i‖≤A) → ‖tariffs (fun i=> V i (b i)) T‖≤ C*A := by
      by_cases h' :∀ i,b i=false
      · obtain ⟨C,hC,H⟩:=diagram F k X w hu hp hx h; refine ⟨_,hC,fun T he ht A B hV hT hA=>?_⟩; simp_rw [h']; rw [show (fun i=>V i false)=(fun i=> assigns (Place.sampled (X i))) from rfl,←severance T he hV hs]; exact H (slate T d n) ht _ (fun i hj hi=> by have he:=hA i hj hi; unfold pearlJ at he; rw [hi] at he; exact he)
      push Not at h'; obtain ⟨i,hi⟩:=h'; obtain ⟨C,hC,J⟩:=sharp_decay a (fun i=> V i (b i)) (fun i=>he i _) i (f i) (hf i) (by simp [V,Bool.eq_true_of_not_eq_false hi]) hs
      exact ⟨_,hC,fun T hp _ A B ht hx _=> J T hp B A ht hx⟩
   choose C hC hD using hz; refine ⟨∑ i,C i,Finset.sum_nonneg (fun i _=>hC i),fun T ht hT A B hA hu hx hV=>?_⟩
   rw [show (fun i=>assigns (U i)) = fun i=> ∑ u:Bool,V i u by funext i; rw [H i, Fintype.sum_bool];rfl,dial V he hs T hu,Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> hD i T ht hT A B hu hx hV)
end YM.FormalBulk08.Grail
