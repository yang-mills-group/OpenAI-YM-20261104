import YM.MSbar.Alto.Patch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge)(V:Fees) (p s r:ℕ)(a:ℝ)(g:Side)
open Cane
variable {α A η D b E :ℝ} {k i j L':ℕ}
lemma chargeMon (hv:0≤D)(hg:0≤ E)(ha:a≤α) : 0 ≤ value a D η E s k∧value a D η E s k ≤ value α D η E s k:=by
   refine ⟨?_,favMon _ _ _ ha hv hg⟩; have hx:=jaws k; have hw:0≤teeth k:=zero_le_one.trans hx; unfold value candle Measuring.factor; positivity
lemma feedMon (hv:0≤D)(hg:0≤E)(ha:a≤α): 0 ≤ feed a η E D s k i ∧ feed a η E D s k i ≤ feed α η E D s k i:=by obtain ⟨ht,hf⟩:= chargeMon s a (k:=k) (η:=η) hv hg ha; unfold feed; have hp:0≤value α D η E s k:=ht.trans hf; constructor; positivity;gcongr
lemma crown_nonneg (hv:0 ≤ D)(hg:0 ≤ E): 0 ≤ crownB G E η D k:=by unfold crownB; positivity
lemma divine (hv:0≤ D)(hg:0≤ E)(ha:a≤α): 0 ≤ lowP G i a D η E s k∧ lowP G i a D η E s k≤ lowP G i α D η E s k:=by
   obtain ⟨ht,hz⟩:= chargeMon s a (k:=k) (η:=η) hv hg ha; obtain ⟨hd,hr⟩:= feedMon s a (k:=k) (η:=η) (i:=i) hv hg ha
   have hp:0≤feed α η E D s k i:=hd.trans hr
   have hh:crownB G E η D k≥0:=crown_nonneg G hv hg; unfold lowP; constructor; positivity; gcongr; exact ht.trans hz
lemma fixer (hv:0≤ D)(hg:0≤ E)(ha:a≤α):0 ≤ fixP G r a D η E s k ∧ fixP G r a D η E s k ≤ fixP G r α D η E s k :=by
   obtain ⟨ht,hz⟩:= chargeMon s a (k:=k) (η:=η) hv hg ha; have hp(i:ℕ):= divine G s a (i:=i) (η:=η) (k:=k) hv hg ha; unfold fixP
   exact ⟨add_nonneg (sum_nonneg fun i _=>hp i|>.1) (sum_nonneg fun i _=> pow_nonneg ht _),add_le_add (sum_le_sum fun i _=>hp i|>.2) (sum_le_sum fun i _=> pow_le_pow_left₀ ht hz _)⟩
lemma filial (hv:0≤D)(hg:0≤E)(ha:a≤α):0≤fixedG G g r a D η E s k ∧ fixedG G g r a D η E s k≤fixedG G g r α D η E s k:=by
    obtain ⟨ht,hz⟩:= chargeMon s a (k:=k) (η:=η) hv hg ha; have hh:crownB G E η D k≥0:=crown_nonneg G hv hg; unfold fixedG; constructor
    · refine sum_nonneg fun i _=>?_ ; unfold aid; have h:= statue_pos G r (i-1); positivity
    apply sum_le_sum; intro i h; unfold aid; have h:= statue_pos G r (i-1); gcongr
lemma tubMon (hp:a≤α): tub G a s p r ≤ tub G α s p r:=by
    unfold tub; refine sum_le_sum fun i hi=>?_ ; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold rugL liftW; have he:0≤ favor G p (i+1):=by unfold favor; have ht:=shade_pos G; positivity
    gcongr
variable (w:ℝ)
lemma parent (h:Host G V g p s α)(hv:a ≤α) (hw:1≤w): spat G V g s r a w  ≤ spat G V g s r α w:=by
   have hf:= fixer G s r a h.ok.2.1 h.ok.2.2 hv (η:=V.pre) (k:=V.axis); have hp:= filial G s r a g (η:=V.pre) (k:=V.axis) h.ok.2.1 h.ok.2.2 hv; let Q:= V.lead Dean w r; have ht:0≤w:=zero_le_one.trans hw
   obtain ⟨hx,h₀,h₁,h₂,h₃⟩:=h.path; have hh:=h.fine.1; have hD:0≤Q:=by unfold Q Fees.lead purse; positivity
   unfold spat Fees.coin chem; refine add_le_add (add_le_add ?_ ?_) (add_le_add (le_refl _) ?_)
   · apply mul_le_mul_of_nonneg_right _ (by unfold purse; positivity); gcongr; exact hf.2
   · exact mul_le_mul_of_nonneg_right hp.2 (mul_nonneg (pow_nonneg ht 4) hD)
   apply mul_le_mul_of_nonneg_left _ (by positivity); unfold sherry; change V.c1^(r+1+1)*( _ * Q) ≤ _; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sum_le_sum ?_) hD) (by positivity); intro i _; gcongr; apply tubMon; gcongr
lemma bureau (h:Host G V g p s a) : ∀ᶠ w:ℝ in atTop,∀ t:ℝ,0 ≤ t→t≤a→∀ x,1 ≤x→w/2 ≤ x → x ≤ w→ Ready V G Dean g s p t x w:=by
   let hS (i:ℕ) (hi:i∈ Finset.Icc 1 p):= steady G V s i a g (mem_Icc.mp hi|>.1) (h.expedient i hi)
   filter_upwards [eventually_ge_atTop (1:ℝ), (Finset.Icc 1 p).eventually_all.mpr hS] with w hw hV t ht hv x hx hg hT; refine ⟨h.spark,h.arity,⟨hx,hT⟩,h.fine.symm, ?_⟩; intro k he hq U X D; obtain ⟨h₁,h₂,h₃⟩:=hV k (Finset.mem_Icc.mpr ⟨he,hq⟩) x hg -- binder intro U X D Y? check
   have hh:spat G V g s k t w≤ _:=parent G V p s k t g w h hv hw
   constructor
   · exact hh.trans h₁
   constructor
   · exact (mul_le_mul_of_nonneg_right (add_le_add_left hh _) (show 0 ≤1+V.bc from add_nonneg zero_le_one h.fine.2)).trans h₂
   exact (add_le_add_left (div_le_div_of_nonneg_right (add_le_add_left hh _) (sq_nonneg _)) _).trans h₃
end YM.MSbar.Alto
