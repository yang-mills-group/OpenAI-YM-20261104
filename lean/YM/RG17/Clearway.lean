import YM.RG17.Meadows
import YM.RG17.Rift
import YM.OPE.Log.Grid
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
variable {WLG:Bid.Worth} {rL:ℕ→ℕ} {doors} (g: Log.LogPackage R.family WLG rL doors)
variable (h:Stands L D s)
include h Z W fx g
lemma ways17 (hp:x∈generic 2): ∃ M:Rift R Z s D x i, ValueStamp home OPE.run M.plan.q:=by
    obtain ⟨m,hm⟩:= leasable R Z fx; obtain ⟨Y,hY⟩:= found ageLarge (R.family.path.levels.fits.mesh) (by norm_num : (0:ℝ) ≤ 1/2)
    obtain ⟨j,w,H'⟩:= grantedWays R Z fx (fun _=>4) (blue R.family i) W h
    obtain ⟨X,hX,q,v,hq,hv,hV⟩:=assuresMeadows R Z fx W (0:Fin 2) (fun _=>4) j Y m g h hm hY; have hl:T ≤ home:= (homes D).comp s.cofinal
    let E(r:ℝ)(f: K → «Cover»)(p:ℕ×ℕ)(y:R.family.label 0):Prop:= MirrorDuty R A r p.1 p.2 (wrap (R.family.side (wheel R.family r) p.2) ∘ f) (fun j=>atRef L 4 r p (w r j)) (q r/2) (X r) (m r) y
    have hs : ∀ᶠ r in interval D s,∀ᶠ p in L.lens,(∃ y,duty R L m Y w q v (baseRail C x r) y r p ∧ E r (baseRail C x r) p y)∧(∃ z,duty R L m Y w q v (nextRail C x 0 i r) z r p∧E r (nextRail C x 0 i r) p z):=by
       filter_upwards [H',hV x (baseRail R.family x) hp ((reachesBase Z fx x).mono_left hl),hV x (nextRail R.family x 0 i) hp ((reachesNext Z fx x 0 i).mono_left hl)] with r hh hu ht
       filter_upwards [hu,ht] with p hu ht; exact ⟨hu (w r) (fun i=>(hh i).1),ht (w r) (fun i=>(hh i).1)⟩
    let S : Calendar17 R Z s D x i:= ⟨m,Y,hm,hY,w,j,H',q,v,hq.zeroCost ageLarge,hv.mono (by norm_num),by
         filter_upwards [hs] with r hr; filter_upwards [hr] with p hh
         obtain ⟨⟨y,hy,_⟩,z,hz,_⟩:= hh; exact ⟨y,z,hy,hz⟩⟩
    exact ⟨⟨S,X,hX,hs⟩,hq⟩

omit h W fx Z g
open OPE.Log
local notation "o"=>home
local notation "t"=> OPE.run
local notation "a"=> R.family.S.a
-- geometry choice: post-readout toll asks (e.g. e natural positive 3)
include g fx Z
lemma atop {Zpay u:ℝ→ℝ}(hZpay:ValueStamp o t Zpay)(hV:ValueStamp o t u)(h:Lookup R m): ∃ l:ℝ→ℕ, Height R.family.S o t l 1 ∧ ValueStamp o t (fun i=>a (l i)/i)∧∀ᶠ i in o,l i < m i∧ Zpay i/Bid.gainChart R.family.path (m i) (l i) < u i:=by
    let f i:= 1+Zpay i/u i; have hf:ValueStamp o t f:= (ValueStamp.const ageLarge one_pos).add ageLarge (hZpay.div hV)
    let y i:= a (m i)*f i^8; have hy: RateIs o t y (-1):= (h.spine.mesh.mul ((hf.pow ageLarge 8).zeroCost ageLarge)).swap (by norm_num)
    obtain ⟨j,hj,hY,hU⟩:= bracket_down ageLarge hy (hy.tends (by norm_num) ageLarge) g
    have hh : ValueStamp o t (fun i=> a (j i)/a (m i)):= by
       apply ((hf.pow ageLarge 8).div hU).congr; filter_upwards [hZpay.profit,hV.profit,hf.profit] with i hV hU hF; change _ /(y i/a (j i))=_; unfold y; have ht:= R.family.S.a_pos (j i); have hu:= R.family.S.a_pos (m i); field_simp -- hf
    have ht':∀ᶠ i in o, j i < m i∧ Zpay i/Bid.gainChart R.family.path (m i) (j i)< u i:=by
       filter_upwards [hY,hV.profit,hZpay.profit] with i hi hu hf
       let g':=Bid.gainChart R.family.path (m i) (j i); let b:= a (j i); let c:=a (m i); have hb:0<b:= R.family.S.a_pos _; have hc:0<c:= R.family.S.a_pos _; let x:=Zpay i/u i; have hx :0<x:= div_pos hf hu; have hπ:f i=1+x:=rfl
       have hh : c*f i^8 ≤ b:= hi.trans (R.family.S.strictAnti.antitone (Nat.le_succ _))
       have hp:x < f i:= by linarith only [hπ]
       have hS:g'^8=b/c:=by
          unfold g' Bid.gainChart Schedule.scale; rw [← Real.exp_nat_mul]; norm_num; change Real.exp (8*(1/8*(-Real.log c+Real.log b)))=_; rw [show (8:ℝ)*(1/8*(-Real.log c+Real.log b))=Real.log (b/c) from by rw [Real.log_div hb.ne' hc.ne']; ring,Real.exp_log (div_pos hb hc)]
       have hv : x < g':= lt_of_pow_lt_pow_left₀ 8 (Real.exp_pos _|>.le) (by rw [hS]; exact (pow_lt_pow_left₀ hp hx.le (by decide)).trans_le ((le_div_iff₀ hc).mpr ((mul_comm _ _).le.trans hh))) -- order₀?
       refine ⟨R.family.S.strictAnti.lt_iff_gt.mp ((lt_mul_of_one_lt_right hc (one_lt_pow₀ (show 1<f i from by linarith only [hπ,hx]) (by decide))).trans_le hh),?_⟩
       apply (div_lt_iff₀ (show 0<g' from Real.exp_pos _)).mpr; exact ((div_lt_iff₀ hu).mp hv).trans_le (mul_comm ..).le
    -- a(m)/i on Θ via lookup. hZpay irrelevant for this lemma; need simple fx for role W q? use beta Stamp needs Height wheel. insert args instead.
    refine ⟨j,hj,?_,ht'⟩
    have hek : ValueStamp o t (fun i=>a (m i)/i):=by
       have hi :(∀ᶠ i in o,i ≤ a (m i)):=by
           filter_upwards [positiveLength,h.log] with i hi he; apply le_trans _ (he.1.1.trans (R.family.S.strictAnti.antitone (Nat.le_succ _))); exact le_mul_of_one_le_right hi.le ((R.family.path.levels.fits.delayed _).le)
       refine ⟨positiveLength.mono (fun i hi=> div_pos (R.family.S.a_pos _) hi), ((betaStamp ageLarge (goingWheel R Z fx)).pow ageLarge 3).up.of_le' (positiveLength.mono fun i hi=>div_pos (R.family.S.a_pos _) hi) ?_, (ValueStamp.const ageLarge one_pos).down.invLe (Eventually.of_forall fun _=> one_pos) ((positiveLength.and hi).mono fun i hi=>(one_le_div hi.1).mpr hi.2)⟩
       filter_upwards [positiveLength,h.log] with i hi he; exact (div_le_iff₀ hi).mpr (he.1.2.trans (mul_comm ..).le)
    apply (hh.mul hek).congr; filter_upwards with i; have hx:= R.family.S.a_pos (m i); exact div_mul_div_cancel₀ hx.ne'
omit g fx Z
-- nat VI meter spend
include Z fx
lemma radValue17 : ValueStamp o t (role C):=by
   let P:= (betaStamp ageLarge (goingWheel R Z fx)); let x:=V; have hp:= P.pow ageLarge 8
   refine ⟨positiveLength.mono (fun i hi=> div_pos (R.family.S.a_pos _) hi), Wallet.from_tends ageLarge (stretches Z fx), hp.up.of_est ?_⟩
   filter_upwards [reverseSpoke C fx Z.simple,positiveLength] with i hi hz
   unfold role; rw [inv_div,Real.norm_of_nonneg (div_pos hz (R.family.S.a_pos _)|>.le)]; exact (div_le_iff₀ (R.family.S.a_pos _)).mpr (hi.trans (mul_comm ..).le)
omit fx
lemma gValue17 : ValueStamp o t Z.g:=by
    have hx:= Z.contour; let s:= Gauge.slopeConstant G; have hs:0<s:= Gauge.slopeConstant_pos Z.simple
    have hp:Tendsto (fun i=>(Z.g i^2*t i)⁻¹) o (𝓝 s):=by simpa only [inv_inv] using! hx.inv₀ ((inv_pos.mpr hs).ne')
    have hu : Wallet o t (fun i=>(Z.g i)⁻¹^2):=by
       apply ((Wallet.from_tends ageLarge hp).mul (Wallet.id ageLarge)).congr; filter_upwards [ageLarge.eventually_gt_atTop 0] with i hi; field_simp -- log & little
    refine ⟨Eventually.of_forall Z.positive, Wallet.from_tends ageLarge Z.vanishes, hu.of_le' (Eventually.of_forall fun i=> inv_pos.mpr (Z.positive i)) ?_⟩
    filter_upwards [Z.vanishes.eventually (ge_mem_nhds zero_lt_one)] with i hi
    exact le_self_pow₀ (one_le_inv₀ (Z.positive i)|>.mpr hi) (by decide)
variable (M:Rift R Z s D x i) (e:ℕ)
include g Z fx
lemma hasTraces17 (hM:ValueStamp o t M.plan.q) : ∃ X:Sparkfare R Z x i M e, ValueStamp o t (fun i=> R.family.S.a (X.l i)/i):=by
   have he : ValueStamp o t (fun i=> V i*Z.g i^(e:ℝ)):=by simp_rw [Real.rpow_natCast]; exact (radValue17 R Z fx).mul ((gValue17 R Z).pow ageLarge e)
   obtain ⟨l,hL,hV,hP⟩:= atop R Z fx M.plan.m g (hM.div (ValueStamp.const ageLarge zero_lt_two)) he M.plan.nearby
   refine ⟨⟨l,hL,?_⟩,hV⟩
   filter_upwards [hP,M.pace.earlier (by norm_num) ageLarge hL] with r hr ht
   exact ⟨ht.le,hr.1, ((Z.fuse_at r).mono_left L.certified|>.rpow_const (.inl (Z.positive r).ne')|>.const_mul (role R.family r)).eventually (le_mem_nhds hr.2)⟩
end YM.RG17
