import YM.WilsonCoeffUV.Reclosure.Selection
/-!
# Lit unmarked representative in the analytic curvature language.

One can reclose from any paid fixed partial lift (using DIFFERENT routes,
kernels, analytic factors of same type... if fully locally re-matched
through the lower orders as below). D-independent grade and exponent.
Fuel arbitrary smaller width if costs fixed. No change to P even in quadratic
base at L>K. Curvature coefficient of positive quadratics has BOTH zero value
and zero offset first deriv in this export (using spin of full P).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary AnalyticNext.QuarticMatch.Estimate Near Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i j k r t:ℕ}{s S a b u v:ℝ}{W X F:Canvas G}

-- iterative extend per grade

def sews (P:SeriesA G)(F: Canvas G)(k:ℕ): Prop:= ∀ i< k,murals P i=F i
def consort (P:SeriesA G)(e k:ℕ):= ∀ i∈P,i.grade=e ∧ i.rise< k

noncomputable def plates (e:ℕ): ℕ→List (ℕ×ℕ)
   | 0=>[]
   | i+1=>(e,i)::plates e i
noncomputable def stiles: ℕ→ List (ℕ×ℕ)
   | 0=>[]
   | i+1=> stiles i ++ plates i (i+1)
def desk (P:SeriesA G):= P.map fun i=> (i.grade,i.rise)
def seals (P:SeriesA G):= ∀ i∈P,Deed i.cells
lemma seals_pair (U V:SeriesA G)(p:seals U)(q:seals V): seals (U++V):= fun i hi=> (List.mem_append.mp hi).elim (p i) (q i)
structure Halo (P:SeriesA G) (F:Canvas G)(i k:ℕ)(s A:ℝ) : Prop where
   same : consort P i k
   holds j: j < k → murals P i (j+2)= F i (j+2)
   lim : P.length=k
   plate: desk P=plates i k
   shoots: seals P
   light : Draw P s A

lemma silence_m {P:SeriesA G}(h:consort P i k)(p:j < i) : murals P j=0:= by
    induction P with
    | nil=> rfl
    | cons x P ih=> simp_rw [murals_cons,Pi.add_apply,presenceV x (show j<x.grade by rw [(h x (List.mem_cons_self ..)).1]; exact p),ih (fun j p=> h _ (List.mem_cons_of_mem _ p)),add_zero]
lemma farLane {P:SeriesA G}(h:consort P i k)(p:k+2≤ j): murals P i j=0:=by
    induction P with
    | nil=> rfl
    | cons x P ih=> obtain ⟨e,b⟩:= h x (List.mem_cons_self ..); rw [murals_cons,Pi.add_apply,Pi.add_apply,zero_lane x (by omega),ih (fun x t=> h _ (List.mem_cons_of_mem _ t)),add_zero]

-- extension width independent F. Ranks bought through all s∈...
lemma sprocket (G:Gauge)(e i:ℕ)(h:i≤e+1)(s:ℝ)(he:0<s): ∃ v C,0<v ∧ v≤s ∧ 0≤ C ∧ ∀ (K:Canvas G) A, 0≤ A→ Desc K e s A→ (∀ i<e,K i=0)→∃ V : SeriesA G,Halo V K e i v (C*A):=by
   induction i with
   | zero=> exact ⟨s,0,he,le_rfl,le_rfl,fun K A h H p=>⟨[], ⟨by simp [consort],by simp,rfl,rfl,by simp [seals],draw_nil (by rw [zero_mul])⟩⟩⟩
   | succ i ih=>
     obtain ⟨v,C,hv,he',hC,w⟩:= ih (by omega)
     obtain ⟨u,D,hp,h',hD,H⟩:= novae G s he e i
     let t:=min v u; refine ⟨t,C+D,lt_min hv hp,(min_le_left ..).trans he',add_nonneg hC hD,?_⟩
     intro P A hA hz hg
     obtain ⟨B,m,y,z,a,b,r⟩:= w P A hA hz hg
     obtain ⟨F,f,F',hx,q⟩:= H A (P e (i+2)) (hz.beats _) (hz.hike _) (hz.hill _) (hz.symr _) (tick_pillar hz.toPointV hg (r:=i+1)) (fun hb=>by subst hb; exact ⟨hz.sign,hz.aft⟩)
     -- drop any unused hx
     let X: PrismA G:=⟨e,i,by omega,F⟩
     have he'Y : recordV X e (i+2)=P e (i+2):= (nimbus X).trans q
     have ht : 0 ≤ (C+D)*A:=by positivity
     refine ⟨X::B,⟨?_,?_,by simp [z],by simp [desk,plates,← a,X],fun i hi=> (List.mem_cons.mp hi).elim (fun h=>h.symm ▸ F') (b i),?_⟩⟩
     · intro j hj; rcases List.mem_cons.mp hj with p|p
       · subst j; exact ⟨rfl,i.lt_succ_self⟩
       exact ⟨(m j p).1, (m j p).2.trans i.lt_succ_self⟩
     · intro j hj; rw [murals_cons,Pi.add_apply,Pi.add_apply]
       by_cases hm:j=i
       · subst j; rw [he'Y,farLane m le_rfl,add_zero]
       rw [zero_lane X (by change (¬ _ ) → i+2+(e-e)≠ j+2; omega),y j (by omega), zero_add]
     constructor; exact ht
     intro j hj; rcases List.mem_cons.mp hj with p|p
     · subst j; exact f.change (min_le_right ..) (mul_le_mul_of_nonneg_right (by linarith) hA)
     exact (r.2 j p).change (min_le_left ..) (mul_le_mul_of_nonneg_right (by linarith) hA)

lemma extHalo {P:SeriesA G} (h:0<s)(g: Halo P F e (e+1) s a)(hp:PointV F e): murals P e= F e:=by
   have hh:= soul h g.light e
   ext1 i
   by_cases H:i≤1 ∨ e+2< i
   · rw [hp.nilV i H, hh.nilV i H]
   obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le' (show 2≤ i by omega); exact g.holds i (by omega)
lemma grow (G:Gauge)(e k:ℕ)(s:ℝ)(hs:0<s) : ∃ v C,0<v ∧ v ≤ s ∧ 0≤ C ∧ ∀ (P:Canvas G) W, fromBefore W e → W.length≤ k→ sews W P e→ ∀ A a, 0≤ A → Desc P e s A→ Draw W s a →∃ Z:SeriesA G, fromBefore (W++Z) (e+1)∧sews (W++Z) P (e+1) ∧ Z.length=e+1 ∧ desk Z=plates e (e+1) ∧ seals Z∧ Draw (W++Z) v (a+C*(A+a)) := by
    let t:=steep s; let Δ:=k*Mosaic.tax G s e
    have he := div_pos hs (by norm_num:0<(4:ℝ)); have hT : t≤ s:=by unfold t steep; linarith
    obtain ⟨v,C,hv,hv',hC,p⟩:= sprocket G e (e+1) le_rfl t he
    have hd:0 ≤ Δ:= mul_nonneg (by positivity) (tax_nn G hs e)
    refine ⟨v,C*(1+Δ),hv,hv'.trans hT,mul_nonneg hC (by linarith),?_⟩
    intro P W eW w z A a hA H hh
    let F:= P-murals W
    have hp:=hh.1; have hz j:j<e→F j=0 := fun q=>by unfold F; simp [z j q]
    have hy : F e 2=P e 2:= by unfold F; simp only [Pi.sub_apply,empty_two eW,sub_zero]
    have hB : 0≤ A + Δ*a:=by positivity
    have hk:F e 2=P e 2:=hy
    have ht:Desc F e t (A+Δ*a):= by
       refine ⟨H.toPointV.sub (soul hs hh e),fun r=>?_,by rw [hy]; exact H.sign, by rw [hy]; exact H.aft⟩
       apply (((H.beats r).mono hT).sub (pollen_sum hs hh e r)).le
       apply add_le_add_right; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr w) (mul_nonneg hp (tax_nn G hs _))).trans_eq (by unfold Δ; ring)
    obtain ⟨V,h'⟩:=p F _ hB ht hz
    refine ⟨V,fromBoth W V (fun i j=>(eW i j).trans e.lt_succ_self) (fun i j=> by rw [(h'.same i j).1]; omega),?_,h'.lim,h'.plate,h'.shoots,?_⟩
    · intro i p'i; rw [murals_append,Pi.add_apply]; by_cases H:i=e
      · subst i; rw [extHalo hv h' ht.toPointV]; unfold F; rw [Pi.sub_apply]; abel
      rw [silence_m h'.same (by omega), z i (by omega), add_zero]
    exact ((hh.light (hv'.trans hT) (le_add_of_nonneg_right (by positivity))).both (h'.light.light le_rfl (by nlinarith only [hp,mul_nonneg hC hp,mul_nonneg (mul_nonneg hC hd) hA])))

-- consumer can instead extend low-grade choices through future after mutation

noncomputable def meterPre : ℕ→ℕ
  | 0=>0
  | i+1=> meterPre i + (i+1)
lemma authored (G:Gauge)(e:ℕ)(s:ℝ)(hs:0<s) : ∃ v C,0<v ∧ v ≤ s ∧ 0≤ C ∧ ∀ (A:ℝ)(F:Canvas G), 0≤ A → (∀ i< e, Desc F i s A) → ∃ W:SeriesA G, fromBefore W e ∧ sews W F e ∧ W.length=meterPre e ∧ desk W=stiles e ∧ seals W ∧ Draw W v (A*C):=by
   induction e with
   | zero=> exact ⟨s,0,hs,le_rfl,le_rfl,fun A F p t=>⟨[],by simp [fromBefore],by simp [sews],rfl,rfl,(fun i h=> (List.not_mem_nil h).elim),draw_nil (by rw [mul_zero])⟩⟩
   | succ e IH=>
     obtain ⟨t,C,ht,hv,hc,H⟩:=IH
     obtain ⟨v,M,h,hv',hM,hx⟩:=grow G e (meterPre e) t ht
     refine ⟨v,C+M*(1+C),h,hv'.trans hv,by positivity,fun A F he w=>?_⟩
     obtain ⟨P,a,b,p,cF,hA,eF⟩:= H A F he (fun i hi=>w i (by omega))
     have hb:=w e (by omega)
     obtain ⟨Q,q,v,f,cQ,hD,g⟩:=hx F P a p.le b A (A*C) he ⟨hb.toPointV,fun i=>(hb.beats i).mono hv,hb.sign,hb.aft⟩ eF
     exact ⟨P++Q,q,v,by rw [List.length_append, f,p,meterPre],by simp [desk, stiles,←cF,←cQ],seals_pair P Q hA hD,g.light le_rfl (le_of_eq (by ring))⟩
end YM.WilsonCoeffUV.Bank.Mosaic
