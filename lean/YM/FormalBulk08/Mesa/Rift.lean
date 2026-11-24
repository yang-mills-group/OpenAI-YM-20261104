import YM.FormalBulk08.Mesa.Lo

/-! Action store, defined in single mesh coupling. Extensive constants discarded. Ward before further resets included. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {r : ℕ} {G : Gauge} {j : ℕ}

abbrev Pot (G : Gauge) := OrbitV (edgeL G)
def sow (T : Pot G) (n : Side) (e : ℕ) : TypeR (wire G n):= ∑ r∈Finset.range (e+2),facade (r+1) (cum 0 n (T e (r+1)))
def stone (T : Pot G) (n : Side) : Pap (wire G n) := PowerSeries.mk (sow T n)
@[simp] lemma sow_coeff (T : Pot G) (n : Side) (e) : coeff e (stone T n)=sow T n e:=by simp [stone]

structure Vivid (T : Pot G) : Prop where
   civil : ∀ j r, Up (T j r)
   agate : ∀ j r, Agate (T j r)
   valence : ∀ j r, T j r≠0 → 0<r ∧ r ≤ j+2 ∧ r%2=j%2

structure Story (T : Pot G) (R : Row (TypeFace 2) (TypeFace 2)) : Prop extends Vivid T where
   ink : T 0 2=setkin G R
   fare : ∀ j r,∃ η C : ℝ,0<η ∧ Bail (fame _) η (T j r) C
   civic : ∀ n,Civic (stone T n)
lemma Vivid.flower {T : Pot G} (h : Vivid T) (e r : ℕ) (i : Fin r) (n : Side) : rancho (stone T n) e r=cum i n (T e r) := by
   rw [rancho,sow_coeff]; apply facade_unique (marble_agate _ _) (cum_agate _ _ _ (h.civil e r) (h.agate e r)); rw [marble_grade];
   unfold sow; simp_rw [map_sum, MvPolynomial.homogeneousComponent_of_mem (facade_grade _ _)];
   cases r with
   | zero=> exact Fin.elim0 i
   | succ r=>
      by_cases he:r<e+2
      · rw [Finset.sum_eq_single r,if_pos rfl];
        · rw [show cum 0 n (T e _)=_ from funext fun v=> cum_root 0 i n v _ (h.civil e _)]
        all_goals simp_all [eq_comm]
      have hl : T e (r+1)=0:= by by_contra H;have hz:=h.valence e (r+1) H;omega
      rw [hl,cum_zero,map_zero];exact Finset.sum_eq_zero fun j hj=>if_neg (by have :=Finset.mem_range.mp hj;omega)
lemma stoned_main {T : Pot G} {R : Row (TypeFace 2) (TypeFace 2)} {η A : ℝ} (hs :0≤η) (hx:0≤A) (hw : R.strip η A) (h : Vivid T) (hg:T 0 2=setkin G R) (n : Side): coeff 0 (stone T n)=crunch (patron G (Precision.K (R.acts n))) := by
    have hh : T 0 1=0:= by by_contra he; have hb:=h.valence _ _ he; omega
    rw [sow_coeff,sow]; norm_num [Finset.sum_range_succ,hh,hg,cum_zero]; rw [setkin_folds G _ hs hx hw,marble_grade, MvPolynomial.homogeneousComponent_eq_self (kinetic_grade _)]
lemma vine_eq {T : Pot G} (h : Vivid T) (n : Side) (f : Pap (wire G n)) (he : ∀ e r (i : Fin r), rancho f e r=cum i n (T e r)) (hp : ∀ e, marble 0 (coeff e f)=0) : f=stone T n := by
   have hz (e l : ℕ) (hh : e+2<l) : marble l (coeff e f)=0 := by
      have hi : T e l=0:=by by_contra hb; have :=h.valence e l hb;omega
      change rancho f e l=0; rw [he e l (⟨0,by omega⟩ : Fin l),hi,cum_zero]
   ext1 e; rw [sow_coeff,←crema _ _ (hz e)]; rw [Finset.sum_range_succ',hp,map_zero,add_zero]; unfold sow; exact Finset.sum_congr rfl fun i _=> by rw [show marble (i+1) _= _ from he e (i+1) 0]

-- formal freedom to expose only finite order and to specialize widths thereafter

def Enter (G : Gauge): Pot G := fun e r=> if 0<r then ∑ p:PlaqAxes, deploy (ashPort G p) (rancho (Canon G) e r) else 0
lemma bend_rank (e r : ℕ) (h : 2+e ≠ r) : rancho (Canon G) e r=0 := by
   rw [rancho,Canon,map_neg,after_one,←canyon_eq, map_neg,canyon_eq, show marble r _=_ from (marble_eq_zero_iff _ _).mpr ?h,neg_zero]
   case h=> rw [MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (Ne.symm h)]
lemma bend {r} (e) (i : Fin r) (n : Side) : rancho (seed G n) e r=cum i n (Enter G e r) := by
   rw [emberseed,rancho,←canyon_eq,map_sum,map_sum,Enter,if_pos (by have :=i.isLt;omega)]; rw [cum_sums _ _ _ _ (fun v _=>obeys _ _ 0) (show (0:ℝ) ≤ 0 from le_rfl)]; exact Finset.sum_congr rfl fun p _=> packet_schedules (Canon G) (ashPort G p) n i e
lemma Vivid.starts : Vivid (Enter G) := by
   refine ⟨fun b r=>?_,fun b r=>?_,fun b r he=>?_⟩
   · unfold Enter; split;apply up_sums _ _ (fun _ _=> parade _ _); exact up_zero _
   · unfold Enter; split;apply Agate.sums _ (fun _ _=> polished _ (marble_agate _ _)); exact agate_zero _
   unfold Enter at he;split at he
   · rename_i hr;by_contra! hh; have he' : 2+b ≠ r:=by omega
     simp_rw [bend_rank b r he', deploy_void,Finset.sum_const_zero] at he; contradiction
   contradiction
lemma ember_vanish (n : Side) (e) : marble 0 (coeff e (seed G n))=0 := by -- binder side
   rw [seed,map_neg,after_one, ←canyon_eq,map_neg,canyon_eq,show marble 0 _= _ from (marble_eq_zero_iff _ _).mpr ?h,neg_zero]
   case h=> rw [MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (by omega)]
lemma top_word (n : Side): seed G n=stone (Enter G) n:= vine_eq Vivid.starts n _ (fun e _ i=>bend e i n) (ember_vanish n)

lemma enter_width (e r : ℕ) (σ : ℝ) : ∃ B, Bail (fame _) σ (Enter G e r) B := by
   unfold Enter; split; exact ⟨_,bail_many _ _ _ (fun _ _=> obeys _ _ _)⟩; exact ⟨_,bail_void ..⟩
lemma kingdom (G : Gauge) (k : ℝ) (hk : 0<k) (hj : 4≤j) : Story (Enter G) (pink k (Train.top j)) := by
   obtain ⟨σ,C,hσ,hC,H,-⟩:=colors G k hk hj
   let M:=pink k (Train.top j); have he : M.strip σ C:= (H _).1; obtain ⟨E,-,hp⟩:= setkin_pay G hσ.le
   obtain ⟨B,hB⟩:= enter_width (G:=G) 0 2 σ
   refine { Vivid.starts (G:=G) with
     ink:=cum_cmp (Vivid.starts.civil _ _) (up_smooth (up_couple _)) σ σ B (E*C) hσ.le hσ.le hB (hp _ _ hC.le he) 0 ?_
     fare:= fun e r=>⟨σ,(enter_width e r σ).choose,hσ,(enter_width e r σ).choose_spec⟩
     civic:= fun n=>top_word (G:=G) n ▸ seed_ward }
   intro n; rw [←bend,setkin_folds G _ hσ.le hC.le he,rancho, seed_first k hk j hj];rfl
end YM.FormalBulk08.Mesa
