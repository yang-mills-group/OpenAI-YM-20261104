import YM.WilsonCoeffUV.Root.Post.ThroughZero
/-!
# Zero filtration: no hidden y cost allowed on spin-in-grade move. Geometry accepted by Crew. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}{I:Cloister G h}{P:Stand (inkPin I)}

def Symbol (F:Frame G h)(v:Alma F)(Y:Single G D)(e:ℕ): Prop:= ∀ i: Alma F, glean F Y e i= (if e=0∧ v=i then 1 else 0)
structure Lit (F:Frame G h)(v:Alma F)(Y:Single G D): Prop where
   born : shellK (valence F v) Y
   spec : Stakes Y
   walk : Symbol F v Y 0
lemma born_cost (F:Frame G h)(v: Alma F)(e)(Y:Single G D)(p:Symbol F v Y e)(i:Alma F): ‖glean F Y e i‖≤ 1:= by rw [p i]; split <;> simp
lemma Lit.castle {v:Alma F}{Y: Single G D}(p: Lit F v Y)(_h0:r= valence F v): Hears F h 1 (Y 0 r) ∧ Slate (Y 0 r) F (weight F v):=by
    have he i (h:valence F i=r): echoS F (Y 0 r) i=glean F Y 0 i:= by rw [g_lone,h]
    refine ⟨⟨zero_le_one,fun i _ v' => by rw [he i v']; exact born_cost F v 0 Y p.walk i⟩,fun j hj=>⟨le_rfl,fun i h v'=>?_⟩⟩
    rw [he i v',p.walk i,if_neg,norm_zero]; rintro ⟨_,rfl⟩; omega
lemma calmS (p:0≤s)(Y:Single G D)(h:Stakes Y)(r): Wing 0 s 0 (Y 0 r):= by
    cases r with
    | zero=> exact le_rfl
    | succ r=> have hv:=roar_le_levy h.vert h.pur (e:=0) (r:=r) (o:=0) (C:=0) (fun _ hi=> by omega) p le_rfl; rw [mul_zero] at hv; exact hv
lemma salute {R:Stand (inkPin I)} (T: Courant I R)(F:Frame G h)(v:Alma F)(Y:Single G D)(u:Lit F v Y)(p:0<s)(hY: Twig 0 s A (Y 0 (valence F v)))(e:dragCup Bank.terrain I.lamp.s X R.Q):
   fanfare I.lamp.path R h Y 0 (valence F v) = hall (inkPin I).patch h (Agate (inkPin I).patch T.line G) (Y 0 (valence F v)):=by
    let B:= I.lamp; let P:= B.path.patch; let C:= max (max B.path.D X) (B.preD/P.L.val)
    let J:=Y 0 (valence F v); let t:= min s B.s; let g:=t/2
    have ht:0<t:= lt_min p B.anger; have hh:0<g:= by unfold g; positivity
    have he:t≤ B.s:= min_le_right ..; have hv:t/P.L.val≤ s:= (div_le_self ht.le (by exact_mod_cast P.L.property)).trans (min_le_left ..)
    have hb:= hall_cross P R.Q R.M J h (u.spec.pur 0 (valence F v)) hY (calmS p.le Y u.spec (valence F v)) R.T R.rule (dragCup.le (R.rolls.mono (he.trans (B.outlet.trans I.lamp.path.holds.le))) (show B.path.D ≤ C from (le_max_left ..).trans (le_max_left ..))) ((e.mono he).le (show X ≤ C from (le_max_right ..).trans (le_max_left ..))) ((T.price.polish.mono he).le (show _ ≤ C from le_max_right ..)) hv hh.le (show g<t from by unfold g; linarith)
    rw [mul_zero,mul_zero] at hb
    rw [fanLead I.lamp.path R h Y u.born,← T.Qmat]; exact sub_eq_zero.mp (wing0 hb)
lemma streak {j:Alma F}{Y:Single G D}(T:Courant I P)(H:Hol G)(hq:h<D)(L:Lit F j Y)(e:dragCup Bank.terrain I.lamp.s X P.Q)(p:0<s)(t: Twig 0 s A (Y 0 (valence F j)))(u:Stakes (fanfare (inkPin I) P h Y))(i:Alma F)(hi:valence F i=valence F j)(v:weight F i≤weight F j):
   glean F (fanfare (inkPin I) P h Y) 0 i= if i=j then ((inkPin I).patch.L.val:ℝ)^(h-weight F j) else 0 := by
   obtain ⟨-,hh⟩:= L.castle (refl (valence F j))
   let D':= (inkPin I).patch;
   let Y0:=Y 0 (valence F j); let Q:= Agate D' T.line G; let a:= min s I.lamp.s
   have hu: Q=P.M:= T.Qmat.symm; have ha:0<a:= lt_min p I.lamp.anger
   have hp: dragCup Bank.terrain a (I.lamp.preD/D'.L.val) Q:= by rw [hu]; exact (T.price.polish.mono (min_le_right ..))
   have hv':a/D'.L.val≤ s:= (div_le_self ha.le (by exact_mod_cast D'.L.property)).trans (min_le_left ..)
   have hr : hall D' h Q Y0=fanfare (inkPin I) P h Y 0 (valence F j):= (salute T F j Y L p t e).symm
   have H':= hall_top H F T.shape T.same (inkPin I).kernel.penalty_pos I.inlet I.horizon hq t (calmS p.le Y L.spec _) hh (weigh_cap F j) (L.spec.m 0 _) (L.spec.pur 0 _) hp ha hv' (hr.symm ▸ u.pur _ _) (hr.symm ▸ u.m _ _) (notar F i) v
   rw [g_lone, hi]; rw [←hr]
   set V:= (D'.L.val:ℝ)^(h-weight F i)
   have hx : trellis F (hall D' h Q Y0) i= V • trellis F Y0 i:= by unfold trellis; rw [hi]; exact congr_fun H' (sheet F i)
   rw [echoS,hx, Complex.smul_re]; change V • echoS F Y0 i=_; rw [show echoS F Y0 i=glean F Y 0 i from (by rw [g_lone,hi]),L.walk]; by_cases h:i=j
   · rw [h,if_pos rfl,if_pos ⟨rfl,rfl⟩, smul_eq_mul,mul_one]; unfold V; rw [h]
   simp [h,Ne.symm h]

-- ceiling exact: position Hub; C_j chosen BEFORE L. independent of Kernel matrices.
lemma quota (H:Hol G)(F:Frame G h)(a k:Alma F)(e:valence F a=valence F k)(u:ℝ)(hx:0<u)(j t:ℕ)(p:4≤j)(hp:4≤t)(v:h≤j)(hq:h<D)(s:ℝ)(ht:0<s): ∃ C:ℝ,0≤C ∧∀ (I:Cloister G h)(P:Stand (inkPin I))(_T:Courant I P)(Y:Single G D), I.lamp.input=s→xota I=u→ I.j=j → I.l=t → Lit F k Y→ Stakes (fanfare (inkPin I) P h Y) → (∃ X:ℝ, dragCup Bank.terrain I.lamp.s X P.Q) → (∃ A:ℝ,Twig 0 I.lamp.input A (Y 0 (valence F k))) →
   ‖glean F (fanfare (inkPin I) P h Y) 0 a‖ ≤ C*((inkPin I).patch.L.val:ℝ)^(h-weight F k):=by
    obtain ⟨C,hc,H'⟩:= hall_dear (valence F k) H F hq (weigh_cap F k) u hx p hp v (notar F a) (weigh_cap F a) s ht
    refine ⟨C,hc,?_⟩; intro I P T Y hh he ht hv l L x t
    obtain ⟨D',hD'⟩:= x; obtain ⟨A,hA⟩:= t
    subst s u j;
    let b:= I.lamp; let K:=b.path.patch; let R:= Agate K T.line G; have hM:= T.Qmat; have hτ:= T.price.polish; have hc' : fanfare I.lamp.path P h Y 0 (valence F k) = hall K h R (Y 0 (valence F k)):= salute T F k Y l b.inlet hA hD'
    obtain ⟨U,V⟩:= l.castle (refl (valence F k)); have hy:= calmS b.inlet.le Y l.spec (valence F k)
    subst_vars
    let c:= Y 0 (valence F k); let Z:= hall K h R c
    rw [g_lone,e]; rw [show fanfare _ _ _ _ _ _= _ from hc',mul_comm]; refine (le_trans (Complex.abs_re_le_norm _) (norm_le_pi_norm (Bell F (weave F a) (valence F a) (arret (brow F a D) Z _ _)) (sheet F a))).trans ?_
    rw [e,show _*C= (K.L.val:ℝ)^(h-weight F k)*C*1 from Eq.symm (mul_one _)]
    exact H' T.g K T.shape _ T.same c A b.s (b.preD/K.L.val) 1 hA b.anger (by change dragCup _ _ _ R; rw [← show P.M=R from T.Qmat]; exact hτ) b.ports (l.spec.pur 0 _) (l.spec.m 0 _) (hy.cap (by linarith)) (fun _=> hy) V U Z rfl (hall_grace _ _ _ _ (l.spec.pur 0 _))
end YM.WilsonCoeffUV.Cosmos
