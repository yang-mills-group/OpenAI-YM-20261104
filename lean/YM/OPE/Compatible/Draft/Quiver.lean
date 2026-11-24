import YM.OPE.Compatible.Navy.Stack
/-!
# Prediction channel on auxiliary shape
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass YM.Stationary
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (S: StepData c f) (H: Even c.val)

local notation "μ" => even_both S.ratio H
protected abbrev rollB := Limb μ ⊕ Limb H
abbrev Tableau (S:StepData c f)(H:Even c.val):= stageScore S.ratio H
lemma gux (v:Tile G (Node μ))(x:Site c): v (crumb μ (S.ratio.embed x)) = v (LiftV S.ratio H (crumb H x)) := by rw [step_node]
lemma accom (u:Tile G (Rill.rollB S H))(t:Tile G (Node μ)):(coat μ ((Tableau S H).dress t u ∘ Sum.inl), coat H ((Tableau S H).dress t u ∘ Sum.inr))=(Lattice.gauge (t ∘ crumb μ) (coat μ (u ∘ Sum.inl)),Lattice.gauge (t ∘ (crumb μ) ∘ S.ratio.embed) (coat H (u ∘ Sum.inr))) :=by -- notation D default remove
     apply Prod.ext -- prod ext
     · exact coat_gauge μ t (u ∘ Sum.inl)
     have he:t ∘ (crumb μ) ∘ S.ratio.embed=(t ∘ LiftV S.ratio H)∘ crumb H:=funext fun _=> gux S H t _
     rw [he]; exact coat_gauge H (t ∘ LiftV S.ratio H) (u∘ Sum.inr)
lemma respect (h:S.patch.Branches S.kernel G)(k:Site f→ G.El)(u:Config G f)(t:S.Choices): S.prediction (Lattice.gauge k u) t=Lattice.gauge (k ∘ S.ratio.embed) (S.prediction u t):=by
      funext i; unfold StepData.prediction; rw [S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2];rfl
lemma caring (h:S.patch.Branches S.kernel G) (k: Site f→G.El)(i:Config G c)(j:Config G f)(q:S.Choices): noiseTaylor S (Lattice.gauge (k∘ S.ratio.embed) i) (Lattice.gauge k j) q=noiseTaylor S i j q :=by
      unfold noiseTaylor; rw [respect S h]; apply congr_arg; apply Finset.sum_congr rfl; intro d _; let t:=k ∘ S.ratio.embed; let Z:= S.prediction j q; change G.price (Lattice.gauge t i d*(Lattice.gauge t Z d)⁻¹)=_; rw [show Lattice.gauge t i d*(Lattice.gauge t Z d)⁻¹=t d.1*(i d*(Z d)⁻¹)*(t d.1)⁻¹ by unfold Lattice.gauge;group,G.price_conj]
@[fun_prop] lemma coatCont : Continuous (coat (K:=G.El) H):= by apply continuous_pi;intro i; unfold coat; split <;> fun_prop
@[simp] lemma coatOne : coat H (K:=G.El) 1=1:= by funext i; simp [coat]
def echo (t:S.Choices)(x:Tile G (Limb μ))(i:Limb H): G.El:= S.prediction (coat μ x) t i.val
lemma echo_odd (h:S.patch.Branches S.kernel G)(t:S.Choices): ∀ᶠ x: Tile G (Limb μ) in 𝓝 1, S.prediction (coat μ x) t=coat H (echo S H t x):=by
     have ht: Tendsto (coat (K:=G.El) μ) (𝓝 1) (𝓝 1):=by simpa only [coatOne] using! (coatCont μ).tendsto 1
     have he:= Work.F04.prediction_germ h
     filter_upwards [ht.eventually (eventually_all.mpr (fun k:S.Choices=>he k t))] with x hx; symm; refine seen_coat H _ ?_; intro i
     have ha:= S.prediction_channel h (axisK i) (offset i c) (coat μ x) t; rw [show (S.prediction (coat μ x) _)=(S.prediction (coat μ x) t) from (show S.prediction (coat μ x) (S.withinChoice (axisK i) (offset i c) t)=S.prediction (coat μ x) t from hx _), offset_step S.ratio H, staying μ x i] at ha; exact ha.symm
lemma cogs (V Y: Tile G (Limb H)) : (∑ p:edgeV c,G.price (coat H V p * (coat H Y p)⁻¹))=4*∑ p:Limb H,G.price (V p*(Y p)⁻¹):=by
      let F(p:edgeV c):=G.price (coat H V p*(coat H Y p)⁻¹); have he(k:Kv)(p:edgeV c): F (ferry k p)=F p:=by
          by_cases h:(axisK k).flip p.2
          · unfold F;unfold coat; rw [Weir.stood,path_ferry]; simp only [h,Bool.true_xor]; cases hx:Weir.dir H p <;> simp only [↓reduceIte,Bool.false_eq_true, Bool.not_true,Bool.not_false, inv_inv]
            · exact twist (V (pathX H p)) (Y (pathX H p))
            exact (twist (V (pathX H p)) (Y (pathX H p))).symm
          unfold F coat; rw [Weir.stood,path_ferry]; simp [h]
      have hx:(∑ p,F p)=4 • ∑ i:Limb H,F i.val:=by convert! (edgesK H).sumRep F (fun i k=> he k i) using 1; congr!
      rw [show _= _ from hx]; unfold F; simp only [rep_coat,nsmul_eq_mul,Nat.cast_ofNat]
where twist (u v:G.El): G.price (u⁻¹*v)=G.price (u*v⁻¹):=by rw [← G.price_inv (u*v⁻¹),show (u*v⁻¹)⁻¹=u*(u⁻¹*v)*u⁻¹ by group,G.price_conj]
end YM.OPE.Cascade.Rill
