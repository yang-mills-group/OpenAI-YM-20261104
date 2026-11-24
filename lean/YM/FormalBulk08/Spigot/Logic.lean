import YM.FormalBulk08.Spigot.Brave
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

variable {M:Cabin D I G r}{l:ℕ}
open MeasureTheory
-- transport budget operations
lemma burse_wash {μ ν:Halo D}{a:ℝ}(hμ:Fleet μ)(hν:Fleet ν)(ha:0≤a)(h:η≤σ) : burse u a η μ ν≤ burse u a σ μ ν:= by
   have he (g:Halo D)(hg:Fleet g)(i:Brush D): stub g u a η i ≤ stub g u a σ i:= by
      let f q:= fun x:Pier=> rush u q (a+‖x.val‖); have hi:=hg i; have hv q: Integrable (f q) (g i):= ((show Continuous (f q) by unfold f rush; fun_prop)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      apply integral_mono (hv _) (hv _) (fun x=>?_) ; unfold f rush; gcongr --
   exact Finset.sum_le_sum (fun i _=>add_le_add (he _ hμ i) (he _ hν i))
lemma Energy.shrink (h:Energy M u σ A)(he:η≤σ)(hs:A ≤ B): Energy M u η B := by
   have ht: SumBudget _ A:= sum_tier h.income (show ∀ i,0≤(M.atoms i).magnitude * burse u (M.atoms i).length η (M.plus i) (M.minus i) from fun i=>mul_nonneg (by unfold Atom.magnitude; positivity) (burse_below u (Nat.cast_nonneg _) (h.plus i) (h.minus i))) (fun i=> mul_le_mul_of_nonneg_left (burse_wash (h.plus i) (h.minus i) (Nat.cast_nonneg _) he) (by unfold Atom.magnitude; positivity))
   exact {h with income:=⟨ht.1,ht.2.1,ht.2.2.trans hs⟩}
def struck (M:Cabin D I G r)(e:ℕ): Anthem D G:= fun p j t=> if e ≤ j ∧ t+e=j+r then candle M p t else 0
lemma struck_here (h:e ≤ E)(hx:t+e=E+r)(p): struck M e p E t=candle M p t:= if_pos ⟨h,hx⟩
lemma struck_now (p): struck M e p e r=candle M p r:= struck_here le_rfl (Nat.add_comm ..) p
lemma struck_right {p:Studio D}(hp:struck M e p E t ≠0): e≤E∧ t+e=E+r:= by contrapose! hp; unfold struck;simp_all
lemma struck_banner (o:Loc G 1)(p:Studio D)(h:Energy M u σ A)(hs:0<σ)(hx:r≤l+e)(n:Side): Kemp.banner l (struck M e p) n=cradle e M p n:= by
   ext1 j; rw [Kemp.banner, coeff_mk,cradle,coeff_X_pow_mul']; split
   next he =>
      rw [Finset.sum_eq_single (j-e+r)]; rotate_left
      · intro b _ hb; rw [show struck M e p j b=0 from Classical.byContradiction (fun h=>by have h':=struck_right h;omega),sieve_zero,map_zero]
      · intro hb; simp only [Finset.mem_range] at hb;omega
      rw [struck_here he (by omega),canon_jet o h hs,Broc.beam_price,after_one, Nat.add_comm (j-e) r]
   next he => exact Finset.sum_eq_zero fun i _=>by rw [show struck M e p j i=0 from Classical.byContradiction (fun k=> he (struck_right k).1),sieve_zero,map_zero]
lemma struck_linear (o:Loc G 1)(h:Energy M u σ A)(hs:0<σ)(hx:r≤l+e): Clef o (struck M e) l:= by
   refine ⟨⟨fun p q=>?_,fun x p=>?_⟩,?_,?_⟩
   · funext i j; simp_rw [Pi.add_apply]; unfold struck; by_cases hv:e ≤ i ∧ j+e=i+r
     · simp_rw [if_pos hv]; exact (candle_linear o h hs j).1 _ _ -- need unfolding rhs
     rw [if_neg hv,if_neg hv,if_neg hv,add_zero]
   · funext i r; simp_rw [Pi.smul_apply]; unfold struck;split_ifs; exact (candle_linear o h hs r).2 x p
     rw [smul_zero]
   · refine ⟨fun p i j hp=> ?_,fun p j t=> ?_,fun j t=>?_⟩
     · unfold Yield; have he:=struck_right hp;omega
     · unfold struck; split; exact candle_turn M p t; exact agate_zero t
     obtain ⟨η,C,hp,hC,H⟩:=candle_bill (I:=I) (D:=D) o r t hs; have ht:= (tsum_nonneg h.income.1).trans h.income.2.2; refine ⟨η,A*C,hp,mul_nonneg ht hC,fun i=>?_⟩; unfold struck; split; exact (H _ _ u h i).bill
     exact (Knox_zeros _).mono (by positivity)
   rw [solo_iff]; intro n p; rw [struck_banner o p h hs hx]; exact cradle_civic o h hs n e p

structure Woodsy (o:Loc G 1)(σ B:ℝ)(E:ℕ)(T:Anthem D G): Prop where
    height:0≤B
    precincts: ∀ e≤ E,∀ r p, Knoxville (fame _) σ (0,o) (T p e r) (B*‖p‖)
lemma income_print (o:Loc G 1)(hs:0<σ)(r e E:ℕ):∃ η C:ℝ,0<η∧0≤C∧∀ (M:Cabin D I G r),∀ u A,Energy M u σ A→Woodsy o η (A*C) E (struck M e):= by
   choose δ K h hk H using fun j=> candle_bill (D:=D) (I:=I) o r j hs; obtain ⟨η,C,he,hC,J⟩:= Broc.finance_family δ K (E+r) h hk; refine ⟨η,C,he,hC,fun M u A hp=> ?_⟩; have ht:= (tsum_nonneg hp.income.1).trans hp.income.2.2; refine ⟨mul_nonneg ht hC,fun i hi j p=>?_⟩; unfold struck;split
   next hx=> obtain ⟨hh,hj⟩:= J j (by omega); exact (penn_shrink (H j _ _ _ hp p).bill hh).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj ht) (norm_nonneg _))
   exact (Knox_zeros _).mono (by positivity)

-- ∑ partition on main, supports rank 0
lemma print_ink (P:Dill)(Q:Herald)(T:Studio D→ₗ[ℝ]Tile (edgeL G) r) (p:Studio D){μ ν:P.Foils G r→Spigot.Halo D}{o:Loc G 1}(U:Link G n) (hs:0<σ)(hB:Energy (Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T)) u σ A)(hp:0<η)(h:Knoxville (fame _) η (0,o) (T p) B)(ht:Torrid (T p) η 0 o)(hx: Lust (T p))(hy:Agate (T p)): Broc.blur (sieve n (T p)) U=traceP U (PowerSeries.coeff r (paste (canon (Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T)) p))):= by
    let M:= Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T);have he:=canon_gain hB hs p U r; let f z:= M.pulse (z:P.Foils G r) p*traceP U (PowerSeries.coeff r (paste (spring (M.atoms z))));have hh:Summable f:= he.summable
    rw [←he.tsum_eq]; change _ = ∑' z,f z; rw [Dill.display P Q U (T p) hp h ht hy]; simp_rw [Dill.chamber_size P Q _ (T p) hx]; rw [hh.tsum_prod,hh.prod.tsum_sigma]; refine tsum_congr (fun w=> ?_); rw [tsum_fintype]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [tsum_fintype]; rfl
lemma print_eq (P:Dill)(Q:Herald)(T:Studio D→ₗ[ℝ]Tile (edgeL G) r){μ ν:P.Foils G r→Spigot.Halo D}{o:Loc G 1}(hs:0<σ)(hB:Energy (Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T)) u σ A)(p:Studio D)(hp:0<η)(h:Knoxville (fame _) η (0,o) (T p) B)(ht:Torrid (T p) η 0 o)(hx: Lust (T p))(hy:Agate (T p)): T p=candle (Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T)) p r:= by
    let M:= Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i T); let S:= candle M p r
    obtain ⟨δ,C,hE,hC,H⟩:=candle_bill (I:=P.Foils G r) (D:=D) o r r hs
    have he n: sieve n (T p)=sieve n S:= by
        refine Broc.blur_inj _ _ (sieve_sand _ _ hy) (sieve_sand _ S (candle_turn M p r)) ?_; funext U; change _=traceP U (facade _ _); refine (print_ink P Q T p U hs hB hp h ht hx hy).trans ?_; unfold S; rw [canon_jet o hB hs, Broc.beam_price]
    refine funext fun v=> tendsto_nhds_unique (sieve_kalm _ h hp.le |>.1 v) (((sieve_kalm _ ((H M A u hB p).bill) hE.le |>.1 v)).congr' (.of_forall fun i=>congr_fun (he i).symm _))
end YM.FormalBulk08.Spigot
