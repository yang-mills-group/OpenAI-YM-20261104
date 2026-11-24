import YM.FormalBulk08.City.Porch

/-! Rooted formal identity in the cover. No period-uniform lower jets. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} (i : hue G) {m p : ℕ} {I J : Type*}

lemma soar {T : Tile (Biglot I) (m+1)} {P : (n:Side)→ Tile (Tor n I) (m+1)} (h : Light T P) (a : Biglot I) : Light (shed T a) (fun n=>shed (P n) (drip n a)) := by
    intro v; have ht:= h (Fin.cons a v); simpa only [shed,Fin.comp_cons] using ht
lemma hail (a : edgeL G) (l : Bool)(k r) : Light (hill i a l k r) (fun n=> hill i (drip n a) l k r) := by
   intro v
   have hb (x : chain (hue G) r) : ∀ᶠ n:Side in atTop, rowD (drip n a)∘x=drip n ∘ v ↔ rowD a ∘ x=v := by
      have he n : rowD (drip n a)∘x=drip n ∘ (rowD a∘x):=rfl
      simp_rw [he]
      filter_upwards [eventually_all.mpr (fun j:Fin r=>boil_drip (v j)),eventually_all.mpr (fun j:Fin r=>boil_drip (rowD a (x j)))] with n hn hm
      exact ⟨fun e=>funext fun j=> ((hm j).symm.trans (congr_arg (boil n) (congr_fun e j))).trans (hn j),fun e=>congr_arg (drip n ∘ ·) e⟩
   apply tendsto_const_nhds.congr';filter_upwards [eventually_all.mpr hb] with n hn; unfold hill;apply Finset.sum_congr rfl; intro j _; by_cases he:rowD a ∘ j=v
   · rw [if_pos he,if_pos ((hn j).mpr he)];rfl
   rw [if_neg he,if_neg (he ∘ (hn j).mp)] -- `∘`
lemma steer {T : Tile (Biglot I) m} {P : (n:Side)→ Tile (Tor n I) m} (h : Light T P) (e : m=p) : Light (lengthen e T) (fun n=>lengthen e (P n)):=by cases e;exact h
lemma ideas {T : J→Tile (Biglot I) m} {P : J→ (n:Side)→ Tile (Tor n I) m} (S : Finset J) (h:∀ j∈S,Light (T j) (P j)) : Light (∑ j∈S,T j) (fun n=>∑ j∈S,P j n) := by intro v;simp_rw [Finset.sum_apply]; exact tendsto_finsetSum _ (fun j hj=>h j hj v)
lemma steer_shape {U : Pot G} {S : (n:Side)→OrbitV (wire G n)} (h : ∀ e r,0<r → Light (U e r) (fun n=> S n e r)) (v : edgeL G) (l : Bool) (k r) : Light (shapeD i v l k r U) (fun n=> shapeD i (drip n v) l k r (S n)) := by
    unfold shapeD; apply ideas; intro a _ ; unfold plaster
    have hh (V: chain (edgeL G) (a.val.1+a.val.2)): Tendsto (fun n=> sand (clutch (shed (S n k.1 (a.val.1+1)) (drip n v)) (hill i (drip n v) l k.2 a.val.2)) (drip n ∘ V)) atTop (𝓝 (sand (clutch (shed (U k.1 (a.val.1+1)) v) (hill i v l k.2 a.val.2)) V)):= by
       unfold sand clutch; exact Tendsto.div_const (tendsto_finsetSum _ (fun j _=> ((soar (h _ _ (by omega)) v) _).mul (hail i v l _ _ _))) _
    exact fun V=> (steer hh (Finset.mem_antidiagonal.mp a.property) V).const_mul _
lemma coastal (x : Cover) (e r : ℕ) (U : Pot G) (S : (n:Side)→Pap (wire G n)) (h : ∀ e r,0<r → Light (U e r) (fun n=> rancho (S n) e r)) (hp : ∀ᶠ n in atTop,Rite (S n) (S n) 1 0) :
    ∑ a∈Finset.antidiagonal e,cruisesD i x a r U=0:= by
    have hj : Light (∑ a∈Finset.antidiagonal e,cruisesD i x a r U) (fun n=> ∑ a∈Finset.antidiagonal e,cruisesD i (wrap n x) a r (rancho (S n))) := by
        apply ideas;intro j _;unfold cruisesD; apply ideas; intro v _;have hh (n : Side) : (backwards (wrap n x) v.1,v)=Lotus.drip n (backwards x v.1,v):= by simp only [backwards,Lotus.drip,map_sub,wrap_step] --
        simp_rw [hh];exact fun a=> (steer_shape i h (x,v) true j r a).add (steer_shape i h (backwards x v.1,v) false j r a)
    have hv(v:Axis) : ∀ᶠ n : Side in atTop, step v ≠ (0:Site n) := by
       filter_upwards [effect (step v),effect 0] with n hn hm H; rw [map_zero] at hm; rw [wrap_step,H,hm] at hn; have hp:=congr_fun hn v;simp at hp
    exact funext fun a=> tendsto_nhds_unique (hj a) (tendsto_const_nhds.congr' (by filter_upwards [hp,eventually_all.mpr hv] with n hn hp; rw [apex _ _ _ _ _ hn hp]; rfl))
-- unpackage rank-
-- set k=0 may price via earlier Ward errors; exact flat.
lemma lead_plaster {T : Tile (edgeL G) (m+1)} (h : Agate T) (l : Bool) (v : edgeL G) :
    plaster i v l 0 (⟨(m,0),by simp⟩ : diagD m) T = ((m+1:ℕ):ℝ) • (((if l then 1 else -1)*dotI i v.2.2) • shed T v) := by
    let Z:= (((if l then 1 else -1)*dotI i v.2.2) • shed T v)
    have he: clutch (shed T v) (hill i v l 0 0)=Z := by
        funext b; rw [clutch,hill_base];exact mul_comm _ _
    have ht: Agate Z:= (h.shed _).smul _
    change ((m+1:ℕ):ℝ) • lengthen (r:=m+0) (l:=m) rfl _= _; rw [he,sand_fixed ht];rfl
lemma shape_first (U : Pot G) (j : ℕ) (h : Agate (U j (m+1))) (v:edgeL G) (l:Bool) : shapeD i v l (j,0) m U = ((m+1:ℕ):ℝ) • (((if l then 1 else -1)*dotI i v.2.2) • shed (U j (m+1)) v) := by
    rw [shapeD,Finset.sum_eq_single (⟨(m,0),by simp⟩ : diagD m)];exact lead_plaster i h l v;swap; · simp
    intro b _ he; have hh:b.val.2≠0:= fun e=> he (Subtype.ext (Prod.ext (by change b.val.1=m; have :=Finset.mem_antidiagonal.mp b.property;omega) e))
    rw [plaster,hill_empty _ v l 0 b.val.2 hh]; rw [show clutch (shed (U j (b.val.1+1)) v) (0:Tile (edgeL G) b.val.2)=0 from ?_,sand_nil,length_void,smul_zero]
    case _=> funext a; simp [clutch]

def riverP (x : Cover) (T : Tile (edgeL G) (m+1)) := ∑ k: TypeFace 1,(shed T (x,k,i)-shed T (backwards x k,k,i))
lemma cruise_head (U : Pot G) (j : ℕ) (h : Agate (U j (m+1))) (x: Cover) : cruisesD i x (j,0) m U =((m+1:ℕ):ℝ) • riverP i x (U j (m+1)) := by
    unfold cruisesD; simp_rw [shape_first _ _ _ h]; unfold riverP;rw [Fintype.sum_prod_type,Finset.smul_sum];apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_eq_single i]; swap;· intro b _ he;simp [dotI,he]
    swap;· simp
    simp [dotI,sub_eq_add_neg,smul_add]
lemma storied {T : Pot G} {M : Row (TypeFace 2) (TypeFace 2)} (h : Story T M) (x : Cover) (e r : ℕ): ∑ a∈Finset.antidiagonal e,cruisesD i x a r T=0 := by
   refine coastal i x e r T (stone T) ?_ (.of_forall fun n=> h.civic n 1 0)
   intro e r he;let j:Fin r:=⟨0,he⟩;simp_rw [h.flower _ r j]; obtain ⟨η,C,hp,hC⟩:= h.fare e r;exact (Bank.stable hp.le (h.civil e r) hC j).1
end YM.FormalBulk08.City
