import YM.X.Bare.Uncut
/-!
Whiteness of every joint smeared array at order zero in the Shop;
parity of continuum correl follows. We don't claim O(a^ξ) in this file.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare.Shop
open Pert Pert.Position Pert.RawLabels PertExtension Maxwell Wick Maxwell.Free Set Function Filter MeasureTheory Labels LatticePT Extra.FD Mixed
open scoped Topology Classical BigOperators ContDiff
variable {G : Gauge} {F:Labels.Frames G} (K:Shop F) {d n : ℕ}
local notation "m" => born (d:=d) F K.H K.S K.hS K.hP
local notation "V" => LatticePT.Word G
lemma electricity_real (x:Points n)(hx:x∈conf n)(v:Fin n→ V) : star (electricity v x)=electricity v x:= by
   rw [←wick_bar hx]; congr; funext a; exact MaxwellReading.pure_e ..
lemma electricity_smear (q:ℕ+)(hq:1<q.val)(v:Fin n→ V)(t:Test n): Tendsto (fun k:ℕ=> series v q k t 0) atTop (𝓝 (t.applyTo (electricity v))):= by
   let A:= tsupport t; let C:=Complex.reCLM; let D:=Complex.imCLM
   have hH (L:ℂ→L[ℝ] ℝ):= Subcell.sweep_limit v q hq (L.continuous.comp t.continuous) t.hasCompactSupport (show A⊆conf n from t.tsupport_subset) (fun x h=> by_contra (fun hb=> h (subset_closure (fun hx=> hb (by rw [comp_apply,hx,map_zero])))))
   have hm (L:ℂ→L[ℝ] ℝ): L (t.applyTo (electricity v))=∫ x:Points n,CutoffFree.realTyped v (L ∘ t) x:= by
       unfold Test.applyTo; rw [← L.integral_comp_comm (t.smearing (K:=electricity v) (fun x hx=> (moment_smooth (G:=G) _ hx).continuousAt.continuousWithinAt))]
       refine integral_congr_ae (Eventually.of_forall fun x=> ?_)
       by_cases hx:x∈conf n; swap; simp [CutoffFree.realTyped,t.vanishes hx]
       let g:=electricity v x; have he : (↑g.re:ℂ)=g:= Complex.conj_eq_iff_re.mp (electricity_real x hx v)
       change L (t x*g)= L (t x)*g.re
       nth_rw 1 [← he,mul_comm,← Complex.real_smul, map_smul,smul_eq_mul,mul_comm]
   have hc := hH C; have hd:= hH D; rw [←hm] at hc hd
   let x:= t.applyTo (electricity v); suffices hz:Tendsto _ atTop (𝓝 ((↑x.re:ℂ)+Complex.I*x.im)) from hz.mono_right (le_of_eq (by rw [mul_comm Complex.I,x.re_add_im]))
   exact ((Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hc).add (tendsto_const_nhds.mul (Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hd)))

lemma address_enroll (q:Labels.Label G d):address F d (enroll F d q)=observable G d q:= by
    change address F d ((Model F).project d ((F.level d).coords q))=_; rw [address_eval,fields_eval]; exact congr_arg (observable G d) ((F.level d).coords.symm_apply_apply q)
lemma electrify (i:(F.level d).Index): electrical (m i)=address F d (enroll F d ((F.level d).basis i)):= by
   rw [address_enroll, ← base_raises F i]; rfl
lemma white_eq (t:Test n)(p:Fin n→E F d): adopt F K.H K.S K.hS K.hP d (fun v=> t.applyTo (electricity v)) p= pureBank F d n t p:= by
   have hm: offspring F K.H K.S K.hS K.hP d (fun v:Fin n→ V=>t.applyTo (electricity v)) =(pureBank F d n t).compLinearMap (fun _=> enroll F d):= by
      refine Module.Basis.ext_multilinear (fun _ : Fin n=> (F.level d).basis) (fun q=>?_)
      let v : Fin n→ (F.level d).Index:=q
      change spread _ _ ((F.level d).basis ∘ q)=t.applyTo (fun z=> visible F d z _); rw [spread_eval]; apply congr_arg _; funext z; rw [visible_eq]; change electricity (m ∘ v) z= Maxwell.Wick.moment G z _; apply congr_arg (Maxwell.Wick.moment G z); exact (funext fun i=> electrify K (v i))
   rw [adopt,hm,MultilinearMap.compLinearMap_apply,MultilinearMap.compLinearMap_apply]
   simp only [physical_round]
lemma bank_white (q:ℕ+)(hq:1<q.val)(s:Pert.Position.Section F d): Tendsto (fun k:ℕ=>lookie F s (K.bank q k d 0)) atTop (𝓝 (lookie F s (pureBank F d))):= by
   change Tendsto (fun k=> adopt _ _ _ _ _ _ _ s.p) _ (𝓝 (pureBank F d s.r s.f s.p)); rw [← white_eq K]; simp_rw [adopt,MultilinearMap.compLinearMap_apply, offspring,spread_value]; exact tendsto_finset_sum _ fun i _=> tendsto_const_nhds.mul (electricity_smear q hq _ s.f)
include K in
lemma all_par : pulls (par F d) (pureBank F d)=pureBank F d:= by
   funext n t; ext1 p; let s:Pert.Position.Section F d:= ⟨n,p,t⟩
   let q: ℕ+:=3; have he:1<q.val:= by decide -- decide? let
   change lookie F s (pulls (par F d) (pureBank F d))=lookie F s (pureBank F d); rw [pulls_at]
   exact tendsto_nhds_unique_of_eventuallyEq (bank_white K q he _) (bank_white K q he s) (Eventually.of_forall fun k=> by dsimp only; rw [← pulls_at,bank_parity K];simp)
end YM.PositionX.Bare.Shop
