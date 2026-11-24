import YM.RG17.Pardon
import YM.UVNext.COUPLING_RESET.Probe
/-! Dual deployment. conditional ledger
 independent series ports not defined by this ratio. No use of physical
 all flag Taylor approximation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "V"=> role R.family
variable (m Y:ℝ→ℕ)(x:Points 2)(i:Axis) (p:ℕ)
local notation "K"=> (Fin 2)
local notation "A"=> (fun _:Fin 2=> (4:ℕ))
local notation "T"=> interval D s
variable (w:podium R) (q v:ℝ→ℝ)
def stamp17 (L:Layout F)(w:podium R) (f: K → «Cover»)(r:ℝ)(j:ℕ×ℕ) (k:ℕ) (hk:k ≤ j.1):ℂ:=
     let o:= wrap (R.family.side (wheel C r) j.2) ∘ f; let u i:=atRef L 4 r j (w r i);
     let Q':=fun U=>liftVac R.family.path j.1 j.2 j.1 U*(∏ i:Fin 2, R.family.O j.1 j.2 (u i) (attachV R (wheel C r) (p:=j.2) o j.1 i) U);
     Push.GridApprox.pushTo R.family.path j.1 j.2 hk Q' 1/liftVac R.family.path j.1 j.2 k 1
structure Metro (Z:Ledger L)(s:Extraction.Sequence)(D:Lenses.Mantle F B)(x:Points 2)(i:Axis) where
    plan : Calendar17 R Z s D x i
    cash : ℝ→ℝ
    X : ℝ→ℕ
    pace : Height R.family.S home OPE.run X (1/2)
    plush : RateLE home OPE.run cash (-1/32)
    measure : ∀ᶠ r in interval D s, ∀ᶠ j in L.lens,∀ ht:X r≤ j.1,
      (∃ y:R.family.label 0,duty R L plan.m plan.Y plan.wage plan.q plan.v (baseRail C x r) y r j ∧ ‖stamp17 R L plan.wage (baseRail C x r) r j (X r) ht-send0 R.family y‖≤cash r) ∧
      (∃ y:R.family.label 0,duty R L plan.m plan.Y plan.wage plan.q plan.v (nextRail C x 0 i r) y r j ∧ ‖stamp17 R L plan.wage (nextRail C x 0 i r) r j (X r) ht-send0 R.family y‖≤cash r)
variable (h:Stands L D s)
include h Z W fx
lemma mounted17 (hp:x∈generic 2): Nonempty (Metro R Z s D x i):=by
    obtain ⟨m,hm⟩:= leasable R Z fx; obtain ⟨Y,hY⟩:= found ageLarge (R.family.path.levels.fits.mesh) (by norm_num : (0:ℝ) ≤ 1/2)
    obtain ⟨j,w,H'⟩:= grantedWays R Z fx (fun _=>4) (blue R.family i) W h
    obtain ⟨X,hX,q,v,c,hq,hv,hc,hV⟩:=assuresDual R Z fx W (0:Fin 2) (fun _=>4) j Y m h hm hY; have hl:T ≤ home:= (homes D).comp s.cofinal
    let E(r:ℝ)(f: K → «Cover»)(p:ℕ×ℕ)(y:R.family.label 0):Prop:= StampDuty R A r p.1 p.2 (wrap (R.family.side (wheel R.family r) p.2) ∘ f) (fun j=>atRef L 4 r p (w r j)) (c r) (X r) y
    have hs : ∀ᶠ r in interval D s,∀ᶠ p in L.lens,(∃ y,duty R L m Y w q v (baseRail C x r) y r p ∧ E r (baseRail C x r) p y)∧(∃ z,duty R L m Y w q v (nextRail C x 0 i r) z r p∧E r (nextRail C x 0 i r) p z):=by
       filter_upwards [H',hV x (baseRail R.family x) hp ((reachesBase Z fx x).mono_left hl),hV x (nextRail R.family x 0 i) hp ((reachesNext Z fx x 0 i).mono_left hl)] with r hh hu ht
       filter_upwards [hu,ht] with p hu ht; exact ⟨hu (w r) (fun i=>(hh i).1),ht (w r) (fun i=>(hh i).1)⟩
    have hx(r p) f y (h:E r f p y) :∀ ht:X r≤p.1, ‖stamp17 R L w f r p (X r) ht-send0 C y‖ ≤ c r:= fun _=> h.prime _ (UVNext.CouplingReset.flags_one _)
    let S : Calendar17 R Z s D x i:= ⟨m,Y,hm,hY,w,j,H',q,v,by convert hq using 1;norm_num,hv.mono (by norm_num),by
         filter_upwards [hs] with r hr; filter_upwards [hr] with p hh
         obtain ⟨⟨y,hy,_⟩,z,hz,_⟩:= hh; exact ⟨y,z,hy,hz⟩⟩
    refine ⟨⟨S,c,X,hX,hc.mono (by norm_num),?_⟩⟩
    filter_upwards [hs] with r hr; filter_upwards [hr] with p hh hp
    obtain ⟨⟨y,hy,hu⟩,z,hz,hz'⟩:= hh; exact ⟨⟨y,hy,hx _ _ _ _ hu hp⟩,z,hz,hx _ _ _ _ hz' hp⟩
variable (U:Metro R Z s D x i)
structure Calibrator {A':Ports R.family}(b:Beam R A' p):Prop where
    -- the Forecast in this explicit k-construction. Need constructive calculations, cfg first-order pullback not replacement.
    mixture : ∃ (a e:ℝ)(k:ℕ),0≤a∧2<e∧∀ᶠ r in interval D s,∀ᶠ j in L.lens,∀ ht:U.X r ≤ j.1,
       ‖stamp17 R L U.plan.wage (nextRail C x 0 i r) r j (U.X r) ht-stamp17 R L U.plan.wage (baseRail C x r) r j (U.X r) ht-(vice (L:=L) R b i r (bee C x 0 i r) j-vice (L:=L) R b i r (ay C x r) j)‖ ≤ role C r*(a*ledgerCoupling L r j ^e*Z.Λ r^k)
omit W h
lemma calibrated17 {A':Ports R.family}(b:Beam R A' p) (hz:Calibrator R Z x i p U b) : Coupon R Z x i p U.plan b:=by
    have hl : T ≤ home:= (homes D).comp s.cofinal
    obtain ⟨a',e,k,he,hk,hV⟩:=hz.mixture
    have hR : RateIs home OPE.run V 0:= ((goingWheel R Z fx).mesh.div (show RateIs home OPE.run id (-1) from loglife (r:=id) (show home ≤ home from le_rfl))).swap (by ring)
    have hx:= U.plush
    have hw : ∀ᶠ r in home,∀ᶠ t in L.lens, U.cash r ≤ (V r)*ledgerCoupling L r t^e:=by
       filter_upwards [(hR.mul (Z.coarse_g.rpow e)).overtakes hx ageLarge (by norm_num),positiveLength] with r hr ht
       exact (((Z.fuse_at r).mono_left L.certified|>.rpow_const (.inl (Z.positive r).ne')|>.const_mul (V r)).eventually (le_mem_nhds hr))
    constructor; refine ⟨a'+2,e,k,by positivity,hk,?_⟩
    filter_upwards [hV,U.measure, hw.filter_mono hl,positiveLength.filter_mono hl] with r hr hU ht hv
    filter_upwards [hr,hU,ht,(large_mesh f (U.X r)).filter_mono L.certified,((Z.fuse_at r).mono_left L.certified).eventually (le_mem_nhds (Z.positive r))] with p hP hm hr hj hx
    obtain ⟨⟨y,hy,hC⟩,z,hz,hC'⟩:= hm hj; refine ⟨y,z,hy,hz,?_⟩
    let Z₀:=stamp17 R L U.plan.wage (baseRail C x r) r p (U.X r) hj; let Z₁:=stamp17 R L U.plan.wage (nextRail C x 0 i r) r p (U.X r) hj; let Y₀:=send0 C y; let Y₁:=send0 C z; let b':=vice (L:=L) R b i r (bee C x 0 i r) p-vice (L:=L) R b i r (ay C x r) p
    change ‖Y₁-Y₀-b'‖ ≤ _;rw [show Y₁-Y₀-b'= (Z₁-Z₀-b')+((Z₀-Y₀)-(Z₁-Y₁)) from by ring]
    have ht : U.cash r ≤ role C r*(ledgerCoupling L r p ^e*Z.Λ r^k):= hr.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hx _) (one_le_pow₀ (Z.above r))) (div_pos (R.family.S.a_pos _) hv|>.le)); exact (norm_add_le ..).trans ((add_le_add (hP hj) ((norm_sub_le ..).trans (add_le_add (hC.trans ht) (hC'.trans ht)))).trans_eq (by ring))
end YM.RG17
