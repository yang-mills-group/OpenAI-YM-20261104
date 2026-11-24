import YM.GradedFar.Increment
/-!
# Always retain identical positions, inputs and comparing moments

Pin centre anywhere. Here `T` arbitrary whenever the layouts in use are already
at the appropriate configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
    {n m h:ℕ} {r T:ℝ}{x:Points n}{y:Points m}

-- `moment_fin` proof compatible (see AllOrder Leading Phases)
lemma atTable {T':Table C.book}(d:Caps n)(v:Labels S d) (h:T'.Hierarchy)(hx:x ∈ conf n):
    S.classMoment T' d x v = OPE.Orbits.moment T' x.ofLp v:=by
    let f:=finCongr (Fintype.card_fin n)
    let g:= (runNames (Fin n)).symm.trans f
    have he:= permuted (T:=T') (a:=v) (y:=x.ofLp) h hx g
    rw [← he]; let t:= fun i=> (⟨d i,v i⟩:S.Tag)
    have ht (m : ℕ) (h:m=n): S.classMoment T' d x v = S.useAt T'
       (points fun i:Fin m=> x.ofLp (Fin.cast h i)) (t ∘ Fin.cast h) := by subst m;rfl
    refine Eq.trans (ht _ (Fintype.card_fin n)) (congr_arg₂ (S.useAt T') (congr_arg points (funext fun i=>?_)) (funext fun i=>?_))
    · change x (f i)= x (g (runNames _ i)); rw [show (g (runNames _ i)) = f i from by simp [g,f]]
    change t (f i) = t (g (runNames (Fin n) i))
    rw [show (g (runNames _ i)) = f i from by simp [g,f]]

lemma atTable_within (ν:Viewers F)(d:Fin n→ℕ)(w:Inputs G d)(o:E4){y:Points n}(hr:0<r)(hy:y∈conf n) :
    S.classMoment (spectator F ν) d (r•y) (labels J r w)=TrueCompact F J ν r o y w := by
    obtain hx:=Work.A05.smul_conf hr hy; rw [atTable (T':=spectator F ν) d _ (spectate F ν) hx, TrueCompact]
    have H : sites o r y = fun i=> (r•y) i+o:= funext (fun i=> add_comm ..); rw [H, carrying (spectate F ν) hx]

abbrev repack (u:ListInput G n h)(v:ListInput G m h): ListInput G (n+m) h:= Fin.append (α:=Sec G h) u v
lemma packing (u:ListInput G (n+m) h):u=repack (fun i:Fin n=>u (Fin.castAdd m i)) (fun i:Fin m=>u (Fin.natAdd n i)):= by
    funext i; unfold repack; refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp
lemma packed (ν:Viewers F) (u:ListInput G n h)(v:ListInput G m h)(o:E4)
    (hr:0<r)(hh:forest x (T • y) ∈ conf (n+m)) :
    frank F J ν h r (forest x (T • y)) (repack u v)= today F J ν o r (r*T) r x y u v:= by
    change S.classMoment (spectator F ν) (Ceiling (n+m) h) _ (labels J r (d:=Ceiling (n+m) h) _)= _; rw [today_apply, atTable_within F J ν _ (repack u v) o hr hh,TrueCompact,whole_observed, Orbits.observed]
    apply Eq.symm; let e : Fin n⊕ Fin m≃Fin (n+m):= finSumFinEquiv; have hx := radius_conf hr o hh
    refine Fork.renameRead e (spectate F ν).laws.toSymmetric hx ?_ ?_
    · funext i; rcases i with i|i <;> simp [sites,e,mul_smul]; -- reorder
    funext i; rcases i with i|i <;> simp [repack,e,labels,Orbits.names]
lemma pack_series (A:Arenas G) {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:Through h d)(he:Through h e)(u:Inputs G d)(v:Inputs G e)
    (hh:forest x (T•y)∈conf (n+m))(ht:0<T)(p:ℕ)(z:ℝ): constantCrop A (-Real.log T) hd he x y p z u v=
    crop p z (sent A h (forest x (T•y)) (repack (GradedFar.raised hd u) (GradedFar.raised he v))):=by
    rw [constantCrop,bothCrop_apply]; congr 1; ext1 i; rw [coeff_mk,cashed A _ hh,squeeze,neg_neg,Real.exp_log ht,
      rawCoeff_apply _ _ _ _ _ _ _ hh]

variable {d:Fin n→ℕ}{e:Fin m→ℕ}
lemma today_pack {hd:Through h d}{he:Through h e}(u:Inputs G d)(v:Inputs G e)(ν:Viewers F)(o:E4)
    (hr:0<r)(hh:forest x (T•y) ∈ conf (n+m))
    (hx:∀ i (u:Sec G (d i)),assign J r h (up (hd i) u)= F.sector.derivatives.rise (hd i) (assign J r (d i) u))
    (hy:∀ i (u:Sec G (e i)),assign J r h (up (he i) u)= F.sector.derivatives.rise (he i) (assign J r (e i) u)) :
    today F J ν o r (r*T) r x y u v= frank F J ν h r (forest x (T•y)) (repack (GradedFar.raised hd u) (GradedFar.raised he v)):=by
    rw [packed F J ν _ _ o hr hh,today_apply,today_apply]; unfold labels GradedFar.raised; simp_rw [hx _ _,hy _ _]
    exact (Fork.whole_include (S:=S) F _ _ ν (d':=Ceiling n h) (e':=Ceiling m h) hd he (labels J r u) (labels J r v) (radius_conf hr o hh)).symm
lemma re_expression (u:Inputs G d)(v:Inputs G e)(ν:Viewers F)(o:E4)(x:Points n)(y:Points m)(r T:ℝ):
    today F J ν o r (r*T) r x y u v=atLength F J ν o r T x y u (fun i=> relative J (r*T) r (e i) (v i)):= by
    rw [atLength,today_apply,today_apply]; congr 1; funext i; exact (atHome J (r*T) r (v i)).symm
end YM.Integration.GradedFar.Tariff
