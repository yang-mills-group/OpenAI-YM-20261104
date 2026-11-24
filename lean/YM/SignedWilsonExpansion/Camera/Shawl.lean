import YM.SignedWilsonExpansion.Camera.Pad
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.SignedWilsonExpansion.Camera
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice Schedules HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Dancer.Shell Dancer.Fort XSpace.Cirrus
open Kane.Tilted Belle Belfry Belfry.ScaleFits StageG
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {d n :ℕ}{X:Initialize G}{ι β:Type}{ℱ:Filter ι}{L: Filter β}{A:Credit} {S:Schedule}
open FVA2.Scale Level Maxwell.Free Future Gauge
variable {C:Family G} {f:Extraction.Order} {S':Table C.book}(F:Final C f S')(W:ℝ→tower S') (H:(Bel C.book).Hierarchy) (lead:Leading F W) {d t k:ℕ}
lemma carries {x:Sec G d}(η:ℝ) : gear C.labels d (Real.exp (-η)) (pre C x)=pre C (Level.Dial d η x):=by
     let q:= (Free.fields C.labels d).symm; let Q:= Level.Dial d (G:=G) η; let B:= Logo G d; have he (i: Toon G d): gear C.labels d ( Real.exp (-η) ) ( q ( B i ) )=q ( Q (B i) ):=by
       rw [show (gear C.labels d (Real.exp (-η))) _= (↑(Real.exp (-η)):ℂ) ^ i.size • q ( B i ) from pulse_logo C _ _, show Q (B i)= _ from (by rw [show B i=theory i from logo i]; exact Level.exact₀ η i : Q (B i)= FVA2.Scale.Extent.token η i.size • B i), _root_.map_smul]
     change gear C.labels d (Real.exp (-η)) (q x)=q (Q x); rw [← B.sum_repr x]; simp_rw [map_sum,map_smul, he]
-- Body in CORE.Light grant. At W.Root only. Coordinates originally Act Beam on f.
structure Shawl (C:Family G) (S:Table C.book)(ι:Type)(W:ℝ→tower S) where
    home : ι→ℝ
    station : ι→Homes.BeamT C
    legs : ι→tower S
variable (A:Shawl C S' ι W) (Y: Ultrafilter (ℕ×ℕ)) {r:ι→ℝ} {ℋ:Filter ι}
abbrev Wall.members (A: Shawl C S' ι W)(i:ι) (d:ℕ):= (W (A.home i) d).trans (A.legs i d).symm  -- Liner Compare.W
abbrev Shawl.capacity (X:Shawl C S' ι W)(i:ι)(t:ℕ) : (Bel C.book).Field t≃ₗ[ℂ] (Bel C.book).Field t:= (W (X.home i) t).trans ( X.legs i t ).symm
structure Shine (r:ι→ℝ)(ℋ:Filter ι)(d:ℕ): Prop where
    pivots : pivotT ℋ r A.home
    lives : Tendsto (fun i=>(A.station i).k) ℋ atTop
    checked : ∀ᶠ i in ℋ,(A.station i).Given (track f) H (A.home i)
    bookTP (t:ℕ): t≤d→∀ᶠ i in ℋ,Coherent H.spin H.spin t (Shawl.capacity W A i t) ∧ Shawl.capacity W A i t ((Bel C.book).unit t)=(Bel C.book).unit t
    gleams {t:ℕ} : t≤d →∀ p:(Bel C.book).Field t,Tendsto (fun i=> Shawl.capacity W A i t p) ℋ (𝓝 p)
    contact {t:ℕ} (p:t≤d) : ∀ᶠ i in ℋ,∀ v:( Bel C.book ).Field t, ∃ y:C.label t,Tendsto (fun j=> (A.station i).microphone j t v) (Y:Filter _) (𝓝 y) ∧ S'.project t y=A.legs i t v -- W gear in formula via bridge
-- need binder A includes W implicit or `variable {W}`? W explicit as occurs in type; Shine header uses f from F phantom?
variable (hr:Tendsto r ℋ trail) (Q:Shine (f:=f) W H A Y r ℋ d)
local notation "σ" => A.home
abbrev jumpY (r:ι→ℝ)(i:ι) := Real.log (A.home i/r i)
abbrev proxy (i:ι)(d:ℕ): FieldEnd G d:= let F:= fields C.labels d; (F.toLinearMap.comp (( Shawl.capacity W A i d ).toLinearMap.comp F.symm.toLinearMap))
abbrev Shawn (r:ι→ℝ)(i:ι)(d:ℕ): FieldEnd G d:= Level.turner ( jumpY W A r i ) (proxy W A i d) -- defined rvs
include Q hr
lemma quotedY : FO ℋ (jumpY W A r):=by
     have hr':∀ᶠ i in ℋ,0<r i:=hr.eventually self_mem_nhdsWithin; refine Kane.Tilted.by_abs (C:=Real.log 2) ( ?_ ); filter_upwards [Q.pivots,hr'] with i hq p; have u: 1≤σ i/r i:= ( one_le_div p ).mpr hq.1; have v:(σ i/r i) ≤2:= (div_le_iff₀ p).mpr hq.2; exact ( abs_of_nonneg ( Real.log_nonneg u ) ).trans_le ( Real.log_le_log (zero_lt_one.trans_le u) v )
lemma passedB : ∀ᶠ i in ℋ, Real.exp (- jumpY W A r i)= r i/σ i:=by
     filter_upwards [Q.pivots,hr.eventually self_mem_nhdsWithin] with i hp p; rw [ Real.exp_neg, jumpY, Real.exp_log ( div_pos ( (show 0<r i from p).trans_le hp.1 ) (show 0<r i from p) ),inv_div ]
lemma harvested (hv:t≤d)(v:Sec G t) : By ℂ ℋ (fun i=> Shawn W A r i t v) v:=by
    let u:= jumpY W A r; let X(i):=proxy W A i t; let B:=fields C.labels t; have he: By ℂ ℋ X 1:=by
       apply SeatsW.byShips; intro p F'; let y:= B.symm p; let Y:= F'.comp B.toLinearMap; have hu:= Y.continuous_of_finiteDimensional.continuousAt.tendsto (x:=y); -- syntax
       have hm:= hu.comp ( Q.gleams hv y ); rw [LinearMap.comp_apply, LinearEquiv.coe_coe,B.apply_symm_apply] at hm; exact hm
    let P'(i):= Level.Dial t (G:=G) (u i); let Q'(i):= Level.Dial t (G:=G) (-u i); have h':= quotedY W H A Y hr Q; have H': Salary ℂ ℋ 1 Q':= boundD (θ:=-u) h'.neg_left t
    let T (i):= Shawn W A r i t-1; have ht: Discount ℂ ℋ 1 T:= sameSalary ( dueLeft ( dueRight ( shine.mpr (show By ℂ ℋ (fun i=> X i-1) 0 from by simpa only [sub_self] using subY he (constant (1:FieldEnd G t))) ) H' ) (boundD h' t) ) ( Eventually.of_forall fun i=> ?_ ) (.refl ..)
    · apply SeatsW.viaY (x:=v) (by simpa only [zero_add] using addY (shine.mp (cheapens ht (LinearMap.applyₗ v))) (constant v)) (Eventually.of_forall fun i=>?_); change (Shawn W A r i t v-v)+v=_; exact sub_add_cancel _ _
    · change Q' i * ( X i -1 ) * P' i = Q' i * X i * P' i-1; exact role1 (D:=FieldEnd G t) _ _ _ ( Level.spring _ )
where role1 {D:Type}[Ring D](A B C:D)(h:A*C=1): A*(B-1)*C=A*B*C-1:=by rw [_root_.mul_sub, _root_.sub_mul, _root_.mul_one,h]
lemma rotatesP (hv:t≤d): ∀ᶠ i in ℋ, Shawn W A r i t ( leaf G t )=leaf G t∧ (∀ s:Signed,∀ u:Sec G t,Shawn W A r i t ( ori s.ortho t u )= ori s.ortho t (Shawn W A r i t u))∧ (∀ x:Sec G t,Shawn W A r i t ( reel t x )=reel t ( Shawn W A r i t x )) := by
    let T:= fields C.labels t; filter_upwards [Q.bookTP _ hv] with i ⟨p,v⟩; let u:= jumpY W A r i; let s:= Shawn W A r i t; let P':= proxy W A i t; let X:= Level.Dial t (G:=G) u; let Y:= Level.Dial t (G:=G) (-u); let A0:= Shawl.capacity W A i t; have he (v): pre C (P' v)= A0 (pre C v):= T.symm_apply_apply _; refine ⟨ (?_),fun a x=> ?_,fun x=>?_⟩
    · have h:P' (leaf G t)=leaf G t:= T.symm.injective (show pre C _=pre C _ from by rw [ he,leafLogo ]; exact v); change Y (P' (X (leaf G t)))=_; rw [show X _=_ from Level.Dial_leaf (d:=t) (G:=G) _, h]; exact Level.Dial_leaf ..
    · have h (v):P' (ori a.ortho t v)=ori a.ortho t (P' v):= T.symm.injective (show pre C _=pre C _ from by rw [he,orientLogo C H.spin, orientLogo C H.spin, he ]; exact p.signed .. ); change Y (P' ( X ( ori a.ortho t x ) ))=_; rw [ Level.Dial_ori (t:=u), h, Level.Dial_ori (-u) ]; rfl
    have h (v):P' (reel t v)=reel t (P' v):= T.symm.injective (show pre C _=pre C _ from by rw [he,reelLogo C H.spin, reelLogo C H.spin, he ]; exact p.stars .. ); change Y (P' ( X ( reel t x ) ))=_; rw [ Level.Dial_real (t:=u), h, Level.Dial_real (-u) ]; rfl
lemma lamp (hv:t≤d): ∀ᶠ i in ℋ,∀ x:Sec G t, A.legs i t ( gear C.labels t (r i/σ i) ( pre C (Shawn W A r i t x )))= walk W (σ i) t (Level.Dial t ( jumpY W A r i ) x):=by
    filter_upwards [passedB W H A Y hr Q ] with i hp x; rw [ ←hp,carries ]; let a:= Shawl.capacity W A i t; let y:= Level.Dial t (jumpY W A r i) x; rw [show Level.Dial t (G:=G) (jumpY W A r i) ( Shawn W A r i t x ) = _ from ( DFunLike.congr_fun ( Level.transfer _ ( proxy W A i t ) ) x ).symm ]; suffices hi: pre C (proxy W A i t y)= a (pre C y) by change A.legs i t (pre C (proxy W A i t y))= _; rw[hi]; exact LinearEquiv.apply_symm_apply ( A.legs i t ) _; -- one-line
    exact LinearEquiv.symm_apply_apply ..
end YM.SignedWilsonExpansion.Camera
