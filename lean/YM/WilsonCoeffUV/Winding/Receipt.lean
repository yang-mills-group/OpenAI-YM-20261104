import YM.WilsonCoeffUV.Winding.Repaint
/-! # Sale on realized Sector. Allow one requested extra address arity. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β T:Type}{V:Type}{G:Gauge}{D k:ι→ℕ}{Ñ:ChartRatio G}{m N i j r e a l:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}{E H:Credit}{Q:Realm G (e+1) E}{R: Levels G}
lemma spunRow {K: Row α β}(h:dragCup Bank.terrain s A (shuttleM K))(v:0<s): K.strip (s/2) (A*sheetPay (s/2)):= by
    intro i j; apply budget_minor (cap_scale (Width.compactPay (s/2) (by positivity)) h.1) (fun _=> by positivity)
    intro y; have he: |K i j y| ≤ A*Real.exp (-s*size y):=by have he:= h.2 (0,i) (y,j); simpa [shuttleM,Bank.terrain] using he
    apply le_trans (mul_le_mul_of_nonneg_left he (by positivity)); rw [mul_left_comm,← Real.exp_add]; apply le_of_eq; congr 2; ring
abbrev needleR (s A:ℝ)(α:Type)[Fintype α]:= (Fintype.card α+1)*Real.exp (s/2)*(A*sheetPay (s/2))
lemma tieWall [Fintype β]{K:Row α β}(h:dragCup Bank.terrain s A (shuttleM K))(v:0<s): Rail (K.acts n) (shuttleM K) (s/16) (needleR s A β):=by
    have ht:=spunRow h v; have hp: 0<s/2:=by positivity
    have hh:= boarding (n:=n) K ht hp (mul_nonneg h.1 (sheetPay_pos _ hp).le)
    rwa [show s/2/8=s/16 from by ring] at hh

abbrev nimbus (I:Gear G): ℝ:= max (max 1 (needleR I.s I.D (Larvae G I.patch.L))) (needleR I.s I.D (Hooks G))
lemma snowM (p:m<N)(w:Usage R Ñ m)(n:Side) : let Z:= w.gear; let K:= R.clock.kernel
    Rail (allotM (weaveFine (ratioN Z.patch.L n) G) (Equiv.refl _) (teller G Z.patch K (roam R N m) n)) (shuttleM (feedA R N m)) (w.s/16) (nimbus Z) ∧
    Rail (allotM (weaveFine (ratioN Z.patch.L n) G) (weaveFine (ratioN Z.patch.L n) G) (mer (G:=G) Z.patch K (freeForms R N (m+1)) n)) (shuttleM (conditional R N m)) (w.s/16) (nimbus Z) ∧
    Rail (precisionC G n (freeForms R N m)) (plain G (freeForms R N m)) (w.s/16) (nimbus Z):=by
    intro T K; obtain ⟨g,x⟩:=w.cardG.shift N N N p le_rfl le_rfl
    have hb:= w.width.trans w.win; have hx:= (w.cardG.kite N N N (by omega) le_rfl le_rfl).oneP
    have hp: (plaster G (freeForms R N m)).acts n= precisionC G n (freeForms R N m) := by
        obtain ⟨t,a,h,v,V⟩:= forms_tail R.clock.kernel.penalty R.clock.kernel.penalty_pos _ (R.clock.adm m)
        ext1 i j; rw [plaster,coloration_act,hBlock_periods h.le ((V R m rfl rfl).1 N)]; rfl
    rw [← hp]; refine ⟨?_,?_,(tieWall hx hb).more (le_max_right ..)⟩
    · let P:=feedA R N m; rw [show allotM (weaveFine (ratioN T.patch.L n) G) (Equiv.refl _) (teller G T.patch K (roam R N m) n)=P.acts n from (feed_period R N m p n (n*T.patch.L) rfl).symm]; exact (tieWall g.oneP hb).more (le_max_right ..)
    let V:=conditional R N m; rw [show allotM (weaveFine (ratioN T.patch.L n) G) (weaveFine (ratioN T.patch.L n) G) (mer (G:=G) T.patch K (freeForms R N (m+1)) n)=V.acts n from ((cond_laws R m N).2.2 n (n*T.patch.L) rfl).symm]; exact (tieWall x.oneP hb).more ((le_max_right ..).trans (le_max_left ..))

-- heights e+ vac occ
abbrev admission (w:ℝ)(e:ℕ):= Finset.univ.inf' Finset.univ_nonempty fun i:Fin (e+3)=>perchA w i.val
abbrev admissionA (I:Gear G)(e:ℕ):=1+∑ i:Fin (e+3),(hinges I.past i.val+1)
lemma admissionSeal (I:Gear G): 1≤ admissionA I e:=le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> add_nonneg (hinge_reserve I.depth i.val).le zero_le_one)
abbrev arborθ (s:ℝ)(I:Gear G)(e:ℕ):= min (s/32) (min (I.s/16) (admission I.past e))
lemma arbor_pos (p:0<s)(I:Gear G)(e:ℕ):0<arborθ s I e:= lt_min (by positivity) (lt_min (div_pos (lt_trans I.price I.holds) (by norm_num)) ((Finset.lt_inf'_iff _).mpr fun i _=>perch_pos I.depth _))

lemma singleSeal (I:Gear G)(e:ℕ)(k:Fin (e+3)): hinges I.past k.val+1≤admissionA I e:=by
    apply le_trans (Finset.single_le_sum (s:= (Finset.univ : Finset (Fin (e+3)))) (f:= fun (i:Fin (e+3))=> hinges I.past i.val+1) (fun (i:Fin (e+3)) _=>add_nonneg (hinge_reserve I.depth i.val).le zero_le_one) (Finset.mem_univ k)); exact le_add_of_nonneg_left zero_le_one
lemma lampG (I:Gear G)(_u:0<s){W:Canvas G}{H:FaceRow} (p:BulkP H W) (e:ℕ)(v:∀ i≤ e,∀ r, Amber Bank.terrain I.past A (W i r)) (g:i ≤ e)(r): Sight (emera W n i r) (W i r) (arborθ s I e) (admissionA I e*A):=by
    have hb:=v i g r; have he:=admissionSeal I (e:=e); have hA:=mul_nonneg (zero_le_one.trans he) hb.1
    cases r with
    | zero=> change Sight (0:Ten ℝ (Co n (Hooks G)) 0) _ _ _; rw [show W i 0=0 from congr_fun (congr_fun p.empty.symm _) 0 |>.trans (if_pos rfl)]; exact Sight.zero.more hA
    | succ r=>
        by_cases z:r+1 > i+2; · change Sight (lagoon (W i (r+1)) n) _ _ _; rw [p.rank _ _ (by omega),lagoon_none]; exact Sight.zero.more hA
        let m: Fin (e+3):=⟨r,by omega⟩; have hx:arborθ s I e≤admission I.past e:= (min_le_right ..).trans (min_le_right ..)
        have ht : admission I.past e≤ perchA I.past r:= Finset.inf'_le (s:= (Finset.univ : Finset (Fin (e+3)))) (fun (i:Fin (e+3))=> perchA I.past i.val) (Finset.mem_univ m)
        refine ((bridgeA (n:=n) hb I.depth (p.center i (r+1))).mono (hx.trans ht)).more ?_
        rw [mul_comm A]; apply mul_le_mul_of_nonneg_right _ hb.1; exact singleSeal I e m

def aerie (s:ℝ)(I: Gear G)(e:ℕ)(p:0<s)(tree:I.patch.Branches I.kernel G)(life:LocalRatio I.angle): Arch G:=⟨I.patch,I.kernel,I.angle,tree,life,arborθ s I e,arbor_pos p I e,nimbus I,(le_max_left ..).trans (le_max_left ..)⟩
abbrev holt (Q: Realm G (e+1) E) (m:ℕ)(p:Q.anchor ≤ m)(s:ℝ)(v:0<s): Arch G:= aerie s (Q.mint m p).gear e v (Q.draws.blocks m 0).branches Q.green
open Realm
def cloVent (L:Realm G (e+1) E) (m N:ℕ)(n:Side)(p:L.anchor ≤ m)(v:m<N)(s:ℝ)(b:0<s): ScrollV e (holt L m p s b) := by
    let A:=L.draws; let Ñ:=L.paid; let B:= L.mint m p; let C:= B.gear; let I:=holt L m p s b; let T:Rally (e+1) 0 C:= ReelTime L (le_refl e) p v le_rfl (le_refl N); let X:=T.x; let P:=actionW A Ñ N (m+1); let W:=emera P; let J:= I.P; have he:I.s ≤ B.s/16:= (min_le_right ..).trans (min_le_left ..)
    refine ⟨n,W,roam A N m,freeForms A N (m+1),freeForms A N m,P,shuttleM (conditional A N m),shuttleM (feedA A N m), (snowM v B n).1.mono he,(snowM v B n).2.1.mono he,(snowM v B n).2.2.mono he,admissionA C e*X,(one_le_mul_of_one_le_of_one_le (admissionSeal _) T.rich),?_⟩
    have hv:= catchment L.draws Ñ L.hG L.green (show m+1≤ N from v); intro i z r
    apply lampG C b hv e _ z r; exact fun j p l=> (T.paid j l (Or.inl (show j< e+1 by omega))).pose
end YM.WilsonCoeffUV.Winding
