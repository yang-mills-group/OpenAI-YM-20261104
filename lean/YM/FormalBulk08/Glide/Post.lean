import YM.FormalBulk08.Glide.South

/-! Combine entire one uncontracted linear π_T from actual tree Wick. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava Bank Stationary Tree Work.F05
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{j t r m:ℕ} {n : Side}{I J Q : Type}
-- associative compositional kernel (invariant inputs), via Kith
lemma serial [Fintype I][Fintype J][Fintype Q](A:Matrix I J ℝ)(B:Matrix J Q ℝ)(T:Tile I r) : pearl B (pearl A T)=pearl (A * B) T:= by
    funext v;unfold pearl; simp_rw [tsum_fintype,Finset.sum_mul, Matrix.mul_apply,Fintype.prod_sum,Finset.mul_sum]; rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro a _; apply Finset.sum_congr rfl; intro b _; rw [Finset.prod_mul_distrib,mul_assoc]
lemma tale_rows [Fintype I][Fintype J][Fintype Q]{T:Tile (Biglot I) r}{P:(n:Side)→Tile (Tor n I) r}(h:Kith η T P){X:Row I J}{W: Row J Q}(a: Fin r)(hs:0<η)(hp:X.strip η A)(hw:W.strip η B)(ha:0≤A)(hb:0≤B):
   pearl (lands W) (pearl (lands X) T)=pearl (lands (composeRows X W)) T := by
    have hx:= water_pearl hp h a hs ha; have he:=water_pearl hw hx a hs hb; have hh:=water_pearl (strip_compose hs.le hp hw) h a hs (by positivity); funext v; apply tendsto_nhds_unique (he.1 v) ((hh.1 v).congr' ?_); refine .of_forall fun i=>?_; dsimp only; rw [acts_compose hs.le hp hw];exact (congr_fun (serial _ _ _) _).symm
variable (F: Flight j t)(V : Lodge F.patch) (G : Gauge) (K : KernelChoices)
def urn (T : Tile (edgeL G) m): Tile (Biglot (BoardL G F.patch V)) m:= pearl (lands (zealand K F V G)) (pearl (lands (pane G F.patch V)) (pearl (lands (winging (Rim G F.patch) (Loc G 1))) (jetty (Bank.scroll F.patch.L (Loc G 1)).symm T)))
lemma urn_project {T:Tile (edgeL G) m} (i : Fin m)(p:Up T)(ht:Bail (fame _) σ T A)(hs:0<η)(hη:η≤ F.patch.L.val*σ)(h: (locating G K F V).strip η B): jetty (coastRight Cover _ _) (urn F V G K T)=pearl (merit (script F V G K)) T := by
    obtain hZ:= Bank.packet_bill F.patch.L hη hs.le ht
    let R:=jetty (Bank.scroll F.patch.L (Loc G 1)).symm T; have he:= stable hs.le (packed_up p F.patch.L) hZ i; have hP:=(pane_pay V η (G:=G)); have hx:= wing_strip (I:=Rim G F.patch) (J:=Loc G 1) η;have hb:=zealandPay K F V h
    have hv:=(le_max_left 1 B);rw [urn,tale_rows (water_pearl hx he i hs zero_le_one) i hs hP hb zero_le_one (zero_le_one.trans hv), tale_rows he i hs hx (strip_compose hs.le hP hb) zero_le_one (by positivity)]
    change jetty _ (pearl _ R)=prism (fun _:Fin m=>merit _) T; exact (tower R T rfl (fun _=> script F V G K)).symm
lemma transverse {U : ℝ}(hc:0≤C)(_hx:0≤U)(m:ℕ) (hs:0<σ)(hp:0≤η)(he:η≤ F.L.val * σ)(h':0<η)(hu: (locating G K F V).strip η U) (hb: (roots G K F V).strip η U)(hg:gauss (Flight.duo K.penalty F).A0 η C (4-m)):
   let Y:=max (max C U) ((Fintype.card (Board G F.patch))*(1*((Fintype.card (BoardL G F.patch V))*(1*max 1 U))))
   ∀ (T:Tile (edgeL G) (m+1)), Agate T→Up T→ ∀ A B:ℝ, Bail (fame _) σ T B→ Bail (fame _) σ (tap T) A→
       Bail (fame _) η ((jetty (coastRight Cover _ _) (urn F V G K T))-pearl (merit (chair F G K)) T)
          ((m+1)*(Real.exp (8*η)*A*(Fintype.card (Co F.L (colorsL G))*(Fintype.card (Loc G 1):ℝ)^m)*(Y+Y)^(m+1))) := by
   intro Y T hz hT A B hB hA
   have hx : (Flight.duo K.penalty F).A0.strip η C:= strip_mono (hg [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..))
   have hC : C ≤ Y := (le_max_left ..).trans (le_max_left ..)
   rw [urn_project F V G K 0 hT hB h' he hu]
   exact boat (literal F V hx h' hc G) hs.le hp he hB hA (strip_mono (script_pay F V hu hp) le_rfl (le_max_right ..)) (strip_mono (grown_budget G _ hc hx) le_rfl hC) (strip_mono hb le_rfl ((le_max_right ..).trans (le_max_left ..))) (hc.trans hC) hz

-- s chosen before F.L always. post wrapper λ includes any dimensions.
lemma anchor_quote (h:0<σ)(hs:0<η)(hc:0≤C)(hm:1≤m): ∃ X:ℝ,0<X∧∀ (P:Patch) (T:Lodge P)(U:ℝ),0≤U →∃ D:ℝ,0<D∧∀ (F:Flight j t) (V:Lodge F.patch), ∀ h:F.patch=P, h ▸ V=T→
   Threshold σ η m F.L → η ≤ F.L.val*σ→ (locating G K F V).strip η U→ (roots G K F V).strip η U → gauss (Flight.duo K.penalty F).A0 η C (4-m)→ ∀ W:Tile (edgeL G) (m+1), Agate W→Up W→ Valed W→∀ A B:ℝ, Bail (fame _) σ W B→ Bail (fame _) σ (tap W) A→ Bail (fame _) η (jetty (coastRight Cover _ _) (urn F V G K W)) (B*(X/(F.L.val:ℝ))+ A * D) := by
    obtain ⟨X,D,hX,hD,H⟩:= captain m hm G h hs.le hc
    refine ⟨max 1 X,lt_max_of_lt_left one_pos,fun P W U hU=>?_⟩
    let Y:=max (max C U) ((Fintype.card (Board G P):ℝ)*(1*((Fintype.card (BoardL G P W):ℝ)*(1*max 1 U))))
    let c:= ((Fintype.card (Co P.L (colorsL G)):ℝ)*(Fintype.card (Loc G 1):ℝ)^m);let R:= D*(P.L.val:ℝ)^3+(m+1)*(Real.exp (8*η)*c*(Y+Y)^(m+1)); refine ⟨max 1 R,lt_max_of_lt_left one_pos,fun F V he hF hT hz ht hx hG T ha hA hl A B hp hZ=>?_⟩
    subst P W
    have he' : gauss (chair F G K) η C (4-m):= by intro l hh; rw [chair, advance_grown]; exact grown_budget G _ (by positivity) (hG l hh)
    have hy:= H F.L hT F.odd (chair F G K) he' T ha hA hl B A hp hZ
    have hw:= transverse F V G K hc hU m h hs.le hz hs ht hx hG T ha hA A B hp hZ
    obtain hv:=hw.add hy; rw [sub_add_cancel] at hv; apply hv.mono; change ((m+1)*(Real.exp (8*η)*A*c*(Y+Y)^(m+1))) + _≤ _; let M:= B*(X/(F.L.val:ℝ)) + A*R
    refine le_trans (le_of_eq (b:=M) ?_) (add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_max_right ..) (by positivity)) hp.1) (mul_le_mul_of_nonneg_left (le_max_right ..) hZ.1)); unfold M R; change _= B*(X/(F.L.val:ℝ))+A*(D*(F.L.val:ℝ)^3+(m+1)*(Real.exp (8*η)*c*(Y+Y)^(m+1)));ring
end YM.FormalBulk08.Glide
