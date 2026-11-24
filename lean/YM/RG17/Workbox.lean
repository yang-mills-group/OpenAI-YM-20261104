import YM.RG17.Zed
import YM.RG17.Coast
/-!
# Paying TO reporting frame, full alphabet (t-core)

The approximate terminal reading paid in that capture. Thus enough for
correlation/OPE point matching VS independent ports there after separately
producing those series on same bill with coherences and calibration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Extraction Word
open SharpGram PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson Next.Rank MergeProof Ribbons ManyCopies Next.UVStress
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a₀"=> R.family.S.a
local notation "T"=>OPE.run
variable {n:ℕ} (d:Fin n→ℕ) (t:ℕ) (b:ℝ→ Fin n→ Cover) {m₀:ℝ→ℕ} (h:Lookup R m₀) (ho:Moored R.family L.level) (hz:Pegs D L)
local notation "M"=> L.level
include W hz
open OPE.Columns RG12 in
lemma beacon {p:ℝ→ S.Field t} {c:ℝ} (ht:RateLE home T p c) : RateLE home T (fun r=>toFrame L t r (p r)) (t + c):=by -- weaker inverse in actual read frame w/literal costs
   let Y:= row L L.level (fun _ _=>LinearEquiv.refl ..)
   have h:=pieces_master Y hz.level (fun d=>RateLE.const ((Y.shift d 0).symm.toContinuousLinearEquiv.toContinuousLinearMap) ageLarge) t p (t+c) (ht.mono (by linarith only))
   obtain ⟨u,hu,hv⟩:=h
   let A :ℝ:=2*Lenses.bonus C t; let B:ℝ:= ((R.family.labels.level t).extra+1:ℕ); apply RateLE.of_norm_le (f:=fun i=> A*(B*‖u i‖)) (((RateLE.const A ageLarge).mul ((RateLE.const B ageLarge).mul hu.norm)).mono (by simp))
   filter_upwards [hv,engineeringPass D L W hz t] with i hi hh; rw [← hi]
   exact (hh.2 (u i)).trans (mul_le_mul_of_nonneg_left (mass_le_norm ..) (mul_nonneg zero_le_two (Lenses.bonused ..)))
include ho h Z fx
lemma pollyTransfer {w:ℝ→R.family.label t}{q:ℝ→ℝ}(he:ValueStamp home T q) (hw:∀ᶠ r in home,∃ (p: Filter (ℕ×ℕ)) (u:ℕ×ℕ→R.family.label t), p.NeBot ∧ p≤L.lens∧ Tendsto u p (𝓝 (w r))∧ ∀ᶠ j in p, quota R.family t (m₀ r) j.1 j.2 (u j)≤ q r * a₀ (m₀ r)^t): Wallet home T (fun r=>toFrame L t r (S.project t (w r))):=by
    let R' (i):=H (Q i)^3*H (M i)^2
    have hBye : Wallet home T R':=by
       refine Wallet.mul (.pow ageLarge ?_ 3) (.pow ageLarge ?_ 2)
       · exact (betaStamp ageLarge (goingWheel R Z fx)).up
       exact (betaStamp ageLarge («C»:=R.family) (show Height R.family.S home T _ 1 from ⟨hz.level.growing,hz.level.nearby⟩)).up
    let l:=Lenses.bonus C t; have hl:0≤l:= Lenses.bonused ..
    apply ((Wallet.const ageLarge (2*l)).mul ((hBye.pow ageLarge (t+1)).mul he.up)).of_est
    filter_upwards [hw,h.log,ho,h.spine.grows.eventually_ge_atTop (R.family.ref t),hz.level.growing.eventually_ge_atTop (R.family.ref t),hz.level.growing.eventually (Load.investors D W t)] with i hi hP hM he hK hh
    obtain ⟨p,u,hJ,hT,hY,hq⟩:=hi; let x:=u
    have hp :∀ᶠ j in p, quota R.family t (M i) j.1 j.2 (u j) ≤ (a₀ (M i))^t*((R' i)^(t+1)*q i):=by
       have hA k:H k ≥1:= ((ι).fits.delayed k).le
       have hz:0<a₀ (m₀ i):= R.family.S.a_pos _
       have hx:0<a₀ (M i):= R.family.S.a_pos _
       have hQ:1 ≤ R' i:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hA _)) (one_le_pow₀ (hA _))
       have hκ: a₀ (m₀ i)/a₀ (M i) ≤ R' i:=(div_le_iff₀ hx).mpr ((hP.1.2.trans (mul_le_mul_of_nonneg_right hM.2 (one_le_pow₀ (hA _) |>.trans' zero_le_one))).trans_eq (by unfold R'; ring))
       filter_upwards [hq,(large_mesh f (m₀ i)).filter_mono (hT.trans L.certified),(large_mesh f (M i)).filter_mono (hT.trans L.certified)] with j hi hp hv using
         ((podQuota W hκ hQ R.makes (x j) he hK hp hv).trans ((mul_le_mul_of_nonneg_left hi (show 0≤ (a₀ (M i) / a₀ (m₀ i))^t * (R' i)^(t+1) from by positivity)).trans_eq (by change (a₀ (M i) / a₀ (m₀ i))^t*(R' i)^(t+1)*(q i*a₀ (m₀ i)^t)=_; rw [div_pow]; field_simp)))
    change ‖(L.frame t i).symm (S.project t (w i))‖ ≤ _; rw [hz.frame]
    exact (hh.2 p hJ (le_trans hT hz.along) u (w i) _ hp hY).trans_eq (by unfold l; change 2*_ / _*(a₀ _^t*((R' i)^(t+1)*q i))=_; have hx:= R.family.S.a_pos (M i); field_simp)
omit h ho
include fx Z
private lemma feeder' : ∀ᶠ r in home,H (M r) ≤ H (Q r)^2:=by
   have ht:= Gauge.slopeConstant_pos Z.simple
   have hV: Tendsto (fun r=> H (M r) / H (Q r)) home (𝓝 1):=by
       have he:= (tollRatio Z.reach).div (tollRatio (opt _ fx Z.simple)) ht.ne'; rw [div_self ht.ne'] at he; apply he.congr'; filter_upwards [ageLarge.eventually_gt_atTop 0] with r hr
       exact div_div_div_cancel_right₀ hr.ne' _ _
   filter_upwards [hV.eventually (ge_mem_nhds one_lt_two), ((Station.hat_rate _ Z.simple).comp (turnsWheel C)).eventually_ge_atTop 2] with r hv hQ
   have hh:0<H (Q r):=zero_lt_one.trans ((ι).fits.delayed _); refine ((div_le_iff₀ hh).mp hv).trans ?_; have hp':2 ≤ H (Q r):= hQ; nlinarith only [hp']
lemma rays'(v:(i:Fin n)→ Free R.family (d i)) : ∃ (i:ℕ)(w:ℝ→(j:Fin n)→ R.family.label (d j)), ∀ᶠ r in home, ∀ j,Paid L r (w r) j ≤ H (Q r)^i ∧ master L _ r (w r j)= L.frame (d j) r (v j):=by
   obtain ⟨w,H'⟩:=individual W hz v
   obtain ⟨i,hi⟩:= (eventually_all.mpr fun j:Fin n=>eventually_ge_atTop (2*Lenses.price (d j)+1)).exists
   refine ⟨i,w,?_⟩
   have hc:Tendsto (fun r=>H (Q r)) home atTop:= (Station.hat_rate _ Z.simple).comp (turnsWheel C)
   filter_upwards [feeder' R Z fx W hz,H',eventually_all.mpr (fun j=>hc.eventually_ge_atTop (2*‖v j‖))] with r hr hC hx j
   have hv: (1:ℝ) ≤ H (Q r):= ((ι).fits.delayed _).le
   refine ⟨(hC.1 j).trans (le_trans ?_ (pow_le_pow_right₀ hv (hi j))),hC.2 j⟩
   have hL := pow_le_pow_left₀ (zero_lt_one.trans ((ι).fits.delayed _)).le hr (Lenses.price (d j))
   rw [← pow_mul] at hL; rw [pow_succ]
   calc _ = H (M r)^ _ * (2 * ‖v j‖) := by ring
        _ ≤ _:= mul_le_mul hL (hx j) (by positivity) (pow_nonneg (zero_le_one.trans hv) _)
include h ho
-- Earn only against true aperture, arbitrary w/need. At trans perturb still need WilsonX meeting; no ghost field predictions. Measurement is same stamped letter, not any projection after propagation onto output quotient.
lemma settledSurf (Hb:∃ u r D,OPE.Log.LogPackage R.family u r D) {v:ℝ→(j:Fin n)→R.family.label (d j)}(P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin){i:ℕ}(j:Fin n)(ht:∀ᶠ r in home,∀ j:Fin n,Paid L r (v r) j≤ H (Q r)^i) : ∃ (α:ℝ)(Y:ℝ→ℕ)(q A:ℝ→ℝ),0<α∧α<1 ∧ Height R.family.S home T Y α ∧ ValueStamp home T q ∧ RateLE home T A (-((t+1/16:ℝ)*(1-α))) ∧ ∀ b:ℝ→Fin n → Cover,∀ x:Points n, x∈generic n→ Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x)→∃ w:ℝ→ R.family.label t,(∀ᶠ r in home,∃ (p':Filter (ℕ×ℕ))(y:ℕ×ℕ→ R.family.label t),p'.NeBot∧p'≤ L.lens∧Tendsto y p' (𝓝 (w r))∧∀ᶠ j in p',readingPrice R d L r (Y r) (m₀ r) (q r) (A r) t (b r) (v r) j (y j)) ∧ Wallet home T (fun i=> toFrame L t i (S.project t (w i))) ∧ RateLE home T (fun r=> toFrame L t r (P.packet t (R.family.S.gridPoint (wheel C r) ∘ b r) (d:=d) (fun j=>master L _ r (v r j)) 0) - toFrame L t r (S.project t (w r))) (-(1/32)):=by
   let α:ℝ:= 1/(32*t+2); have ha:0<α:=by unfold α; positivity
   have hβ:α<1:=by
                     unfold α; have hx:(t:ℝ)≥0:=by positivity
                     have ht:(32:ℝ)*t+2>1:=by linarith
                     exact (div_lt_one (by linarith)).mpr ht -- syntax
   obtain ⟨Y,hY⟩:= found ageLarge (ι).fits.mesh ha.le
   obtain ⟨q,A,hq,hA,hW⟩:= buys_words R Z fx W d t Y _ hY hβ j Hb h ho ht
   refine ⟨α,Y,q,A,ha,hβ,hY,hq,hA,fun b x hx hX=>?_⟩
   have hV:= hW b x hx hX; rw [eventually_iff_exists_mem] at hV; obtain ⟨X,hX',hκ⟩:= hV
   choose! y w hw using hκ; have hs:∀ᶠ r in home,∃ (y:ℕ×ℕ→ R.family.label t)(φ:Filter (ℕ×ℕ)), φ.NeBot ∧ φ≤L.lens∧ Tendsto y φ (𝓝 (w r))∧ ∀ᶠ p in φ, readingPrice R d L r (Y r) (m₀ r) (q r) (A r) t (b r) (v r) p (y p):= mem_of_superset hX' (fun r hr=> ⟨_,hw r hr⟩)
   refine ⟨w,hs.mono (fun i hi=>by obtain ⟨y,x,hU⟩:=hi; exact ⟨x,y,hU⟩), pollyTransfer R Z fx W t h ho hz hq (hs.mono fun i hi=>by obtain ⟨p,φ,hφ,hQ,hy,hX⟩:= hi; exact ⟨φ,p,hφ,hQ,hy,hX.mono fun i hi=>hi.measure⟩),?_⟩
   have ht:= beacon R W t hz (yields_reads R Z fx W d t b Y m₀ A w q v hY ha hβ ht hX hx h hA P hs)
   refine (ht.congr (Eventually.of_forall (fun i=> (map_sub ..)))).mono (le_of_eq ?_)
   change t + - ((t + 1/16:ℝ)*(1-α))= _; have hx: 0 <32*(t:ℝ)+2:=by positivity
   unfold α; field_simp; ring
end YM.RG17
