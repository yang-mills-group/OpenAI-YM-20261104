import YM.FormalBulk08.Chapel.Bread

/-! Multilinear installs, none of these vary columns with w. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C : ℝ}{m r:ℕ}{L : Side}{I J Q: Type}

def prism (S:Fin m→ I→J→ℝ) (T:Tile I m) : Tile J m:= fun v=> ∑' w,T w*∏ i,S i (w i) (v i)
lemma tower (U:Tile (Biglot (Co L I)) m)(T:Tile (Biglot I) m) (h: U=jetty (Bank.scroll L I).symm T) (M : Fin m→Cross L I J): prism (fun i=>merit (M i)) T = prism (fun i=> lands (M i)) U := by
   subst U;ext1 v;unfold prism;rw [← Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl (Fin m)) (Bank.scroll L I).symm) (fun w=>T w*∏ i,merit (M i) (w i) (v i))];apply tsum_congr;intro j;congr 1;apply Finset.prod_congr rfl;intro a _;change merit (M a) ((Bank.scroll L I).symm _) _= _; rw [merit,(Bank.scroll L I).apply_symm_apply];rfl

variable [Fintype I][Fintype J]
lemma pack_end (M: Fin r→Row I J){A:Fin r→ℝ}
    (hs:0≤η)(h:∀ i,(M i).strip η (A i))(he:∀ i,0≤A i)(T:Tile (Biglot I) r)(H:Bail (fame _) η T C) (P:ℝ)(hp':0≤P)(hq: ∏ i,A i ≤ P):
    Fling (fame _) η (fun v w=> T w *∏ i,lands (M i) (w i) (v i)) (C*((Fintype.card I)*((Fintype.card J)^(r-1):ℝ))*P) := by
    have hc:= H.1; refine ⟨by positivity,fun i p=>?_⟩; let n:= (Fintype.card I:ℝ);let m:= (Fintype.card J:ℝ); have hm:0≤m:=Nat.cast_nonneg _; have hn:0≤n:=Nat.cast_nonneg _
    apply le_trans (lamp_counts T (fun i=>lands (M i)) (bridge I J η hs) C (fun i=>m*A i) (fun i=>n*A i) i p H (fun i=> grad_line _ (h i) (he i)))
    change ENNReal.ofReal 1*_ ≤ _; rw [ENNReal.ofReal_one,one_mul,←ENNReal.ofReal_prod_of_nonneg (fun j _=> mul_nonneg hm (he j)),←ENNReal.ofReal_mul hc,←ENNReal.ofReal_mul (mul_nonneg hc (mul_nonneg hn (he _)))]; refine ENNReal.ofReal_le_ofReal ?_; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin];
    have h':C*(n*A i)*(m^(r-1)*∏ j∈Finset.univ.erase i,A j)= C*(n*m^(r-1))*∏ i,A i:= by rw [←Finset.mul_prod_erase (Finset.univ: Finset (Fin r)) A (Finset.mem_univ i)];ring
    rw [h'];exact mul_le_mul_of_nonneg_left hq (by positivity)

lemma sides (hs:0≤η)(h0:η ≤ L.val*σ) (S:Fin r→Cross L I J)(A:Fin r→ℝ)(p:ℝ)(h:∀ i, Row.strip (S i) η (A i))(ha:∀ i, 0≤A i)(hb:0≤p)(he: ∏ i,A i≤p)(T:Tile (Biglot I) r)(H:Bail (fame _) σ T C):
    Bail (fame _) η (prism (fun i=>merit (S i)) T) (Real.exp (8*η)*C*(Fintype.card (Co L I)*(Fintype.card J:ℝ)^(r-1))*p):= by
    rw [tower _ T rfl S]; exact (pack_end S hs h ha _ (Bank.packet_bill L h0 hs H) p hb he).bail
-- summability with no root
omit [Fintype I] [Fintype J] in
lemma lenses {I J: Type*}(w:chain J r)(f : Fin r→I→J→ℝ)(H:∀ i j,Summable fun v=> f i v j) (T:Tile I r)(h:∀ v,‖T v‖≤C): Summable (fun v:chain I r=> T v * ∏ i,f i (v i) (w i)):= by
   apply Summable.of_norm_bounded (g:=fun v=>C*∏ i,‖f i (v i) (w i)‖) ?_ ?_
   · apply Summable.mul_left
     have he i : (∑' v, ENNReal.ofReal ‖f i v (w i)‖) ≠ ⊤:= (H i _).norm.tsum_ofReal_ne_top
     refine (ENNReal.summable_toReal (f:=fun v:chain I r=>∏ i,ENNReal.ofReal ‖f i (v i) (w i)‖) (by rw [eun_tsum (fun i v=>ENNReal.ofReal ‖f i v (w i)‖)]; exact ENNReal.prod_ne_top fun i _=>he i)).congr ?_
     intro v;simp only [ENNReal.toReal_prod]; exact Finset.prod_congr rfl fun i _=> ENNReal.toReal_ofReal (norm_nonneg _)
   intro v; rw [_root_.norm_mul,norm_prod]; exact mul_le_mul_of_nonneg_right (h _) (Finset.prod_nonneg (fun _ _=>norm_nonneg _))

lemma twin_arcs (H : 0≤η)(hc:0≤C)(T:Tile (Biglot I) m)(h:Bail (fame I) η T B)(a : Fin m){U R:Row I J}(hU:U.strip η C)(hR:R.strip η C)(P : Fin m→ Row I J)(hp:∀ i, (P i).strip η C):
   prism (fun i=> lands (update P a U i)) T-prism (fun i=> lands (update P a R i)) T = prism (fun i=> lands (update P a (minusRows U R) i)) T:= by
   funext v; rw [Pi.sub_apply];
   have he (U:Row I J)(hh:U.strip η C) : Summable (fun w=> T w*∏ i,lands (update P a U i) (w i) (v i)):= by
       apply (pack_end (update P a U) H _ (fun _=>hc) T h _ (pow_nonneg hc m) ?le).summable H a v
       · intro i; by_cases hx:i=a <;> simp [hx,hh,hp]
       simp
   unfold prism;rw [←Summable.tsum_sub (he U hU) (he R hR)];apply tsum_congr;intro j
   have he (X:Row I J): ∏ i, lands (update P a X i) (j i) (v i)= lands X (j a) (v a)* ∏ i∈Finset.univ.erase a, lands (P i) (j i) (v i):= by
       rw [← Finset.mul_prod_erase (Finset.univ:Finset (Fin m)) _ (Finset.mem_univ a),update_self]; congr 1;exact Finset.prod_congr rfl fun i hi=>by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
   simp_rw [he]; simp only [lands,minusRows];ring
end YM.FormalBulk08.Glide
