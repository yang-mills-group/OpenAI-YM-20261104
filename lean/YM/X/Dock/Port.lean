import YM.X.Dock.Turn
/-!
# customs amateur. normalized *detached* microlenses, includes at χ derivative.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k d:ℕ} {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] {n:Side} {q:ℕ+}{r R e c:ℝ} {A B:Scaff}{φ γ:E4→ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
variable (hq:1<q.val)
lemma dominates {f:Mist V}{g:E4→V}(hr:R≥0) (h:Visa q R 1 (-3) f)(he:Starboard q R f){w:ℕ→ Finset Cover}(hw:∀ᶠ i in L,Frugal (f i) (w i))(hg:∀ x:E4,x≠0→Tendsto (fun i=> (ε i ^(-4:ℤ)) • mosaic (ε i) (f i) x) L (𝓝 (g x))):Integrable g:= by
    let F(k:ℕ):=(ε k^(-4:ℤ)) • mosaic (ε k) (f k); obtain ⟨C,hC,he⟩:= mosaic_dom hr h he; apply enough (f:=F) (Integrable.const_mul axis_int C) (hw.mono (fun i hi=> AEStronglyMeasurable.const_smul (mosaic_ok (epsilon_pos q i) hi).aestronglyMeasurable _)) he; filter_upwards [Measure.ae_ne volume (0:E4)] with z hz; exact hg z hz
-- point & visa in actual natural normalization
structure Focus (q:ℕ+)(R:ℝ)(d:ℤ)(u:Mist ℝ)(φ:E4→ℝ):Prop where
  bank : Visa q R d d u
  foot(a:E4)(Z:Fielding.Walk)(hz:plot q Z a)(ha:a≠0)(hp:‖a‖≤R): Tendsto (fun i=>u i (Z i)) atTop (𝓝 (φ a))
variable (χ:Floor R){j j':ℤ} {u v:Mist ℝ}
namespace Focus
lemma lower (h:Focus q r j u φ)(he:R≤r):Focus q R j u φ:= ⟨Visa.station R h.bank he,fun a z hz ha hr=> h.foot a z hz ha (hr.trans he)⟩
lemma rise(hq:1<q.val)(h:Focus q r j u φ)(hr:0≤r)(he:j'≤j):Focus q r j' u φ:= ⟨Visa.stretch hq h.bank hr he (by omega),h.foot⟩
lemma mix (h: Focus q R j u φ)(ht:Focus q R j' v γ):Focus q R (j+j') (u*v) (fun x=>φ x*γ x):= ⟨h.bank.mulR ht.bank,fun a z hz he hp=> (h.foot a z hz he hp).mul (ht.foot a z hz he hp)⟩
lemma diff (h:Focus q R j u φ)(ht:Focus q R j v γ):Focus q R j (u-v) (fun x=>φ x-γ x):=⟨h.bank.sub ht.bank,fun a z hz he hp=> (h.foot a z hz he hp).sub (ht.foot a z hz he hp)⟩
lemma plus (h:Focus q R j u φ)(ht:Focus q R j v γ):Focus q R j (u+v) (φ+γ):=⟨h.bank.add ht.bank,fun a z hz he hp=> (h.foot a z hz he hp).add (ht.foot a z hz he hp)⟩
lemma neg (h:Focus q R j u φ):Focus q R j (-u) (-φ):= ⟨h.bank.neg,fun a z hz he hp=> (h.foot a z hz he hp).neg⟩
include hq
lemma zoomed (h:Focus q R (-3) u φ)(hr:R≥0)(he:Starboard q R u){w:ℕ→ Finset Cover}(hw:∀ᶠ i in L,Frugal (u i) (w i))(hp:∀ z:E4,R<‖z‖→ φ z=0): Integrable φ ∧ Tendsto (fun i=> ε i ^4 * ∑ z∈w i,u i z) L (𝓝 (∫ z:E4,φ z)):= by
    let v:= fun (i:ℕ)(z:Cover)=> (ε i)^(4:ℤ) • u i z; have hv: Visa q R 1 (-3) v:= Visa.asPow (c:= (4:ℤ)) (q:=q) h.bank; have hs : Starboard q R v:= he.mono (fun i hi z hz=> hi z (fun h=>hz (show v i z=0 by unfold v; rw [h,smul_zero]))); have hW:∀ᶠ i in L,Frugal (v i) (w i):= hw.mono (fun i hi z hz=> hi (fun h=> (hz (show v i z=0 from by unfold v;rw [show u i z=0 from h,smul_zero])))) -- args frug
    have hz(x:E4)(he:x≠0): Tendsto (fun i=>ε i ^(-4:ℤ) • mosaic (ε i) (v i) x) L (𝓝 (φ x)) := by
         let z:= fun i=>index (ε i) x; have hz: plot q z x:= entrant hq x; unfold mosaic v; simp only [smul_smul,zpow_neg,inv_mul_cancel₀ ((zpow_pos (epsilon_pos q _) _).ne'),one_smul]; rcases le_or_gt ‖x‖ R with hr|hR; · exact h.foot x z hz he hr
         rw [hp x hR]; refine tendsto_const_nhds.congr' ?_; -- outside
         filter_upwards [hz.norm.eventually (lt_mem_nhds hR), (show Starboard q R u from by assumption)] with i hi hj; by_contra hn; exact not_le_of_gt hi (gate_range R (by assumption) _ (hj _ (Ne.symm hn)))
    refine ⟨dominates hr hv hs hW hz,(dom_budget hr hv hW hs hz).congr fun i=>?_⟩; simp only [v,zpow_ofNat,smul_eq_mul, Finset.mul_sum]
omit hq
end Focus
variable (w:ℕ→Lane)
abbrev tipMask (w:Floor R)(q:ℕ+)(t:Fielding.Walk): Rhyme q:=fun i z=> w.s (spot (epsilon q i) (lift (z-transit q t i)))
abbrev divideW (q:ℕ+)(a:ℕ→Lane)(u:Mist ℝ)(k:ℕ): ℝ:= epsilon q k^4 * influx a u k
abbrev shutter (f:ℕ→ Lane):Mist ℝ:= fun i z=> f i z
lemma scatter {e:Fielding.Walk}(f:Rhyme q)(h:∀ z∈(Floor.maskL q χ k).support,lift (wrap (side q k) z)=z): galley (ε k) ((tipMask χ q e*f) k)= divideW q (Floor.maskL q χ) (pin q e f) k:=by
   unfold divideW galley influx; congr 1; rw [← lift_band _ h]; let t:= transit q e k; conv_lhs=> rw [← Equiv.sum_comp (Equiv.addRight t)]
   refine Finset.sum_congr rfl fun i _=>?_ ; unfold tipMask; simp only [Pi.mul_apply,show Equiv.addRight t i=i+t from rfl,pin,Floor.masking χ,wrap_lift,t, smul_eq_mul,add_sub_cancel_left, add_comm i _]
variable (X:Fielding.Walk){x:E4}
include hq
lemma magnify_mask (h:Focus q R (-3) u φ): Integrable (fun x=>χ.s x*φ x) ∧ Tendsto (divideW q (Floor.maskL q χ) u) L (𝓝 (∫ x:E4,χ.s x*φ x)):= by
    let v:=Floor.maskL q χ; have hp: Focus q R 0 (shutter v) χ.s:= ⟨Floor.mask_visa hq χ R χ.positive.le,fun _ z hz hx hr=>χ.s.continuous.continuousAt.tendsto.comp hz⟩; refine Focus.zoomed hq (show Focus q R (-3) (shutter v*u) _ from hp.mix h) χ.positive.le (star_smul (f:=u) _ (χ.onboard hq)) (Eventually.of_forall (posed v)) (fun z hz=>?_); rw [χ.s.zero_of_le_dist,zero_mul];rw [dist_zero_right]; linarith [χ.h,χ.s.rOut_pos]
lemma own (h:Atlas q d A φ)(hx:plot q X x)(hr:R≥0): Focus q R (-((2+d:ℕ):ℤ)) (pin q X (run q X d A)) (fun a=>φ (x-(x+a))):= ⟨within hq h.mark X hr,fun _ z hz he _=> street_point h hx hx hz (fun e=>he (by simpa using e.symm))⟩
lemma elseF {y:E4}(h:Atlas q d A φ)(Z:Fielding.Walk)(hx:plot q X x)(hz:plot q Z y)(hr:R≥0)(H:R<‖x-y‖): Focus q R 0 (pin q Z (run q X d A)) (fun a=>φ (x-(y+a))):= ⟨outside hq hx hz h hr H,fun _ z hv _ hc=>street_point h hx hz hv (gone H hc)⟩
end YM.PositionX.Chir.Dock
